{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Coo.REPL.Inside where

import qualified Coo.Grammar.Lexer as G

import qualified Coo.Source.Syntax as S
import qualified Coo.Source.Parse as S
import qualified Coo.Source.Polarity as S
import qualified Coo.Source.Simplify as S
import qualified Coo.Source.Desugar as S
import Coo.Source.Print ()

import Coo.DualCore.Syntax as DC
import Coo.DualCore.Sugar as DC
import Coo.DualCore.Focus as DC
import Coo.DualCore.Polarity as DC
import Coo.DualCore.Run as DC
import Coo.DualCore.Print

import Coo.Data.Namespace

import qualified Data.Text as Txt
import Text.Megaparsec
-- import Text.Pretty.Simple (pPrint)
import Prettyprinter
import Prettyprinter.Render.Text

import Data.Void
import Data.Fixed (mod')
import qualified Data.Map as M
import Data.IORef

import Control.Monad (forever)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Catch

import System.Exit
import System.Console.Haskeline
import System.Console.Haskeline.History

type ExecId = S.CoreId

type ExecCmd = DC.Cmd ExecId S.Literal DC.Strat

type ExecTrm = DC.Trm ExecId S.Literal DC.Strat

type ExecRsp = DC.Rsp ExecId S.Literal DC.Strat

type ExecVal = DC.Val ExecId S.Literal DC.Strat OpIO Void

type ExecCls = DC.Cls ExecId S.Literal DC.Strat OpIO Void

type ExecPat = DC.Pat S.Literal ExecId ExecId

type PrimPat = DC.Pat PatDesc () ()

data PatDesc
  = SpecificLit S.Literal
  | AnyInt
  | AnyFlt
  | AnyNum
  | AnyStr
  | CustomPat String
  deriving (Show, Eq)

instance Pretty PatDesc where
  pretty (SpecificLit i) = pretty i
  pretty AnyInt = pretty "_:integer"
  pretty AnyFlt = pretty "_:float"
  pretty AnyNum = pretty "_:number"
  pretty AnyStr = pretty "_:string"
  pretty (CustomPat desc) = pretty "_:" <> pretty desc

data PrimOp x i o a m
  = POp { opName :: String,
          applyOp :: Strat -> Val x i o (PrimOp x i o a m) a
                  -> m (Cmd x i o) }

instance Eq (PrimOp x i o a m) where
  f == g = opName f == opName g

instance Show (PrimOp x i o a m) where
  show op = "<#" ++ opName op ++ "#>"

instance Pretty (PrimOp x i o a m) where
  pretty = viaShow

type POp m = PrimOp ExecId S.Literal DC.Strat Void (ReplT m)

type OpIO = POp PromptIO

type Glob m = DC.Global ExecId S.Literal DC.Strat (POp m) Void (ReplT m)

type GlobIO = Glob PromptIO

data ReplState = RS { lineno :: Int,
                      polarSource  :: S.PolInEnv,
                      checkpoint :: GlobIO }

data ReplError
  = ParseErr (ParseErrorBundle String Void)
  | SourcePolarityErr S.PolarityError
  | DesugarErr S.DesugarError
  | DualPolarityErr (DC.PolarityError S.CoreId S.Literal)
  | RuntimeErr ExecError
  deriving (Show)

data ExecError
  = UnhandledPattern DC.Strat [ExecPat] ExecVal
  | UnhandledPrimArg String [PrimPat] ExecVal
  | ExpectedData DC.Strat ExecTrm ExecTrm
  | ExpectedCode DC.Strat ExecTrm ExecVal
  | UndefinedData ExecId
  | UndefinedCode ExecId
  | IlldefinedData ExecId DC.Strat ExecCls
  | IlldefinedCode ExecId DC.Strat ExecVal
  deriving (Show)

instance Pretty ReplError where
  pretty (ParseErr err) = hsep
    [ pretty "Parse Error:",
      pretty (errorBundlePretty err) ]
  pretty (SourcePolarityErr err) = hsep
    [ pretty "Polarity Error:",
      pretty err ]
  pretty (DualPolarityErr err) = hsep
    [ pretty "Polarity Error (internal):",
      pretty err ]
  pretty (DesugarErr err) = hsep
    [ pretty "Desugaring Error:",
      pretty err ]
  pretty (RuntimeErr err) = hsep
    [ pretty "Runtime Error:",
      pretty err ]

instance Pretty ExecError where
  pretty (UnhandledPattern o ps v) = vsep
    [ pretty "Unhandled" <+> errKind,
      pretty "Found:" <+> prettyShortVal v,
      pretty "Expected:" <+> align (vsep $ prettyBlankPat <$> ps) ]
    where errKind = case o of
            CBV -> pretty "data structure"
            CBN -> pretty "object message"
  pretty (UnhandledPrimArg name ps v) = vsep
    [ pretty "Unhandled argument to" <+> pretty name <+> pretty "operation.",
      pretty "Found:" <+> prettyShortVal v,
      pretty "Expected:" <+> align (vsep $ prettyBlankPat <$> ps) ]
  pretty (ExpectedData o t u) = vsep
    [ pretty "Expected a data-creating action in the"
      <+> pretty o
      <+> pretty "interaction:",
      pretty "Action:" <+> pretty t,
      pretty "Reaction:" <+> pretty u ] 
  pretty (ExpectedCode o t v) = vsep
    [ pretty "Expected (co)pattern-matching code in the"
      <+> pretty o
      <+> pretty "interaction:",
      pretty "Reaction:" <+> pretty t,
      pretty "Structure:" <+> prettyShortVal v ]
  pretty (UndefinedData x) =
    pretty "Undefined value for:" <+> pretty x
  pretty (UndefinedCode x) =
    pretty "Undefined function for:" <+> pretty x
  pretty (IlldefinedData x o l) = vsep
    [ pretty o <+> pretty "variable" <+> pretty x
      <+> pretty "used as a data structure, but it was defined as code:",
      indent 4 $ prettyShortCls l ]
  pretty (IlldefinedCode x o v) = vsep
    [ pretty o <+> pretty "variable" <+> pretty x
      <+> pretty "used as code, but it was defined as a data structure:",
      indent 4 $ prettyShortVal v ]

newtype ReplT m a
  = ReplT { doReplT :: ExceptT ReplError (StateT (Glob m) (StateT ReplState m)) a }
  deriving (Functor, Applicative, Monad, MonadIO,
            MonadError ReplError,
            MonadState (Glob m),
            MonadReader r,
            MonadMask,
            MonadCatch,
            MonadThrow)

type ReplIO = ReplT PromptIO

type PromptIO = ReaderT Checkpoint (InputT IO)

data Checkpoint = Save { execEnv :: IORef GlobIO,
                         replState :: IORef ReplState,
                         prevHistory :: IORef History }

runReplT :: (Functor m)
         => ReplT m a
         -> Glob m
         -> ReplState
         -> m (Either ReplError a, (Glob m, ReplState))
runReplT (ReplT m) env0 rs0
  = reassocResult <$> runStateT (runStateT (runExceptT m) env0) rs0
  where reassocResult ((a, env'), rs') = (a, (env', rs'))

runReplIOinit :: ReplIO a -> PromptIO (Either ReplError a, (Glob PromptIO, ReplState))
runReplIOinit m = runReplT m initGlob initRS

runPromptIO :: Checkpoint -> PromptIO a -> IO a
runPromptIO chk m = runInputT defaultSettings (runReaderT m chk)

runPromptIOinit :: PromptIO a -> IO a
runPromptIOinit m = do
  globr <- newIORef initGlob
  rsr <- newIORef initRS
  hsr <- newIORef emptyHistory
  runPromptIO (Save globr rsr hsr) m

liftReplState :: Monad m => StateT ReplState m a -> ReplT m a
liftReplState m = ReplT $ lift $ lift m

liftPrompt :: PromptIO a -> ReplIO a
liftPrompt m = ReplT $ lift $ lift $ lift m

liftInput :: InputT IO a -> ReplIO a
liftInput m = liftPrompt $ lift m

overInput :: (forall a. InputT IO a -> InputT IO a)
          -> ReplIO a -> ReplIO a
overInput f (ReplT m) = ReplT $
  ExceptT $
  StateT $ \env ->
  StateT $ \rs ->
  ReaderT $ \chk ->
  f (runReaderT (runStateT (runStateT (runExceptT m) env) rs) chk)

initEnv :: Env ExecId S.Literal DC.Strat OpIO Void
initEnv = M.fromList
  [ (External $ Txt.pack "==", LetFun CBN $ Free equalityOp),
    (External $ Txt.pack "/=", LetFun CBN $ Free notEqualityOp),
    (External $ Txt.pack "<", LetFun CBN $ Free lessThanOp),
    (External $ Txt.pack ">", LetFun CBN $ Free greaterThanOp),
    (External $ Txt.pack "=<", LetFun CBN $ Free lessEqualOp),
    (External $ Txt.pack ">=", LetFun CBN $ Free greaterEqualOp),
    (External $ Txt.pack "+", LetFun CBN $ Free plusOp),
    (External $ Txt.pack "-", LetFun CBN $ Free minusOp),
    (External $ Txt.pack "*", LetFun CBN $ Free timesOp),
    (External $ Txt.pack "/", LetFun CBN $ Free divideOp),
    (External $ Txt.pack "%", LetFun CBN $ Free moduloOp),
    (External $ Txt.pack "^", LetFun CBN $ Free exponentOp),
    (External $ Txt.pack "round", LetFun CBN $ Free roundOp),
    (External $ Txt.pack "ceiling", LetFun CBN $ Free ceilingOp),
    (External $ Txt.pack "floor", LetFun CBN $ Free floorOp),
    (External $ Txt.pack "print", LetFun CBN $ Free printOp),
    (External $ Txt.pack "pprint", LetFun CBN $ Free pprintOp),
    (External $ Txt.pack "run_file", LetFun CBN $ Free runFileOp)]

initPolarity :: S.PolInEnv
initPolarity = S.PolIn $ M.fromList
  [ (S.Bound $ Txt.pack "==", S.CBN),
    (S.Bound $ Txt.pack "/=", S.CBN),
    (S.Bound $ Txt.pack "<", S.CBN),
    (S.Bound $ Txt.pack ">", S.CBN),
    (S.Bound $ Txt.pack "=<", S.CBN),
    (S.Bound $ Txt.pack ">=", S.CBN),
    (S.Bound $ Txt.pack "+", S.CBN),
    (S.Bound $ Txt.pack "-", S.CBN),
    (S.Bound $ Txt.pack "*", S.CBN),
    (S.Bound $ Txt.pack "/", S.CBN),
    (S.Bound $ Txt.pack "%", S.CBN),
    (S.Bound $ Txt.pack "^", S.CBN),
    (S.Bound $ Txt.pack "round", S.CBN),
    (S.Bound $ Txt.pack "ceiling", S.CBN),
    (S.Bound $ Txt.pack "floor", S.CBN),
    (S.Bound $ Txt.pack "print", S.CBN),
    (S.Bound $ Txt.pack "pprint", S.CBN),
    (S.Bound $ Txt.pack "run_file", S.CBN)]

initGlob :: GlobIO
initGlob = DC.Global { DC.extern = replHandlers,
                       DC.locals = initEnv,
                       DC.focusing = initFocus }

initFocus :: FocusSettings Strat ExecId Int
initFocus = DC.FocAs { DC.fociNote = DC.stratFoci CBV,
                       DC.tempZero = 0,
                       DC.nameTemp = Internal . DC.Temp,
                       DC.nameHere = Internal DC.It }

initRS :: ReplState
initRS = RS { lineno = 0, polarSource = initPolarity, checkpoint = initGlob }

initCmd :: ExecCmd
initCmd = DC.Cut DC.NilVal DC.CBV (DC.Var (Internal DC.Join))

replTop :: IO r
replTop = do
  globr <- newIORef initGlob
  rsr <- newIORef initRS
  hsr <- newIORef emptyHistory
  let chk = Save globr rsr hsr
  runPromptIO chk $ runReplIOinit replStart
  forever (runPromptIO chk $ runReplIOinit $ replRestart)

replStart :: ReplIO ()
replStart = do
  captureNextJoin
  checkpointSave
  overInput withInterrupt replLoop

replRestart :: ReplIO ()
replRestart = do
  checkpointReload
  overInput withInterrupt replLoop

replLoop :: ReplIO ()
replLoop =
  handleInterrupt
  (liftIO $ putStrLn "...")
  (DC.loop initCmd -- DC.loopBy printStep initCmd
   `catchError`
   \err -> do
     liftIO $ putDoc $ pretty err <> hardline
     checkpointLoad
     replLoop)

printStep m = do
  liftIO $ putStrLn "=== Next command step ==="
  c <- m
  liftIO $ putDoc $ pretty c <> hardline
  liftIO $ putStrLn "<<<<<<<<<<<<<<<<<<<<<<<<<"
  env <- locals <$> get
  liftIO $ putDoc $ prettyEnv env <> hardline
  liftIO $ putStrLn ">>>>>>>>>>>>>>>>>>>>>>>>>"
  liftIO $ putStrLn "========================="
  return c
  

replNextPOp :: ReplState -> OpIO
replNextPOp rs = POp { opName = "repl#" ++ show (lineno rs),
                       applyOp = \_ -> replNext rs }

replNext :: ReplState -> ExecVal -> ReplIO ExecCmd
replNext rs v = do
  checkpointSave
  printVal v
  nextCommand rs

printVal :: ExecVal -> ReplIO ()
printVal (Struc MT) = return ()
printVal v          = liftIO $ putDoc $ prettyShortVal v <> hardline

nextCommand :: ReplState -> ReplIO ExecCmd
nextCommand rs = do
  resetReplPrompt rs
  input <- gatherInput (lineno rs)
  sc <- replParse (lineno rs) input
  -- liftIO $ putStrLn "--- Parsed source code ---"
  -- liftIO $ putDoc $ pretty sc <> hardline
  -- liftIO $ putStrLn "--------------------------"
  sp <- replPolar sc
  -- liftIO $ putStrLn "--- Polarized source code ---"
  -- liftIO $ putDoc $ pretty sp <> hardline
  -- liftIO $ putStrLn "-----------------------------"
  let smp = S.simplifyReactsCmd sp
  -- liftIO $ putStrLn "--- Simplified source code ---"
  -- liftIO $ putDoc $ pretty smp <> hardline
  -- liftIO $ putStrLn "------------------------------"
  dc <- replTrans smp
  -- liftIO $ putStrLn "--- Desugared Dual Core command ---"
  -- liftIO $ putDoc $ pretty dc <> hardline
  -- liftIO $ putStrLn "-----------------------------------"
  ec <- prepExec dc
  -- liftIO $ putStrLn "--- Executable Dual Core command ---"
  -- liftIO $ putDoc $ pretty ec <> hardline
  -- liftIO $ putStrLn "------------------------------------"
  glob <- get
  let fc = runFocus (focusCmd ec) (focusing glob)
  -- liftIO $ putStrLn "--- Focused Dual Core command ---"
  -- liftIO $ putDoc $ pretty fc <> hardline
  -- liftIO $ putStrLn "-----------------------------------"
  incrementLineno
  captureNextJoin
  return fc

{-
gatherInput :: Int -> ReplIO String
gatherInput ln = liftIO $ do
  putStr $ show ln ++ "> "
  hFlush stdout
  getLine
-}

data ReplAside = BeginMultiLine
               | EndMultiLine
               | ExecuteFile String
               | ReplHelp
  deriving (Show, Eq)

gatherInput :: Int -> ReplIO String
gatherInput ln = gatherMultiLineInput ln Nothing

gatherMultiLineInput :: Int -> Maybe [String] -> ReplIO String
gatherMultiLineInput ln more = do
  let prompt = case more of
        Nothing -> show ln ++ "> "
        Just _  -> show ln ++ "| "
  line <- liftInput $ getInputLine prompt
  case line of
    Nothing  -> liftIO exitSuccess
    Just txt -> do
      case (more, parse (G.whole replAside) ("repl line " ++ show ln) txt) of
        (Nothing,   Left _) -> return txt
        (Just prev, Left _) -> gatherMultiLineInput ln (Just $ txt:prev)
        (Just prev, Right EndMultiLine) -> return $ unlines $ reverse prev
        (Nothing,   Right EndMultiLine) -> do
          liftIO $ putStrLn "not currently reading a multi-line statement"
          gatherMultiLineInput ln more
        (Nothing, Right BeginMultiLine) -> gatherMultiLineInput ln (Just [])
        (Just _,  Right BeginMultiLine) -> do
          liftIO $ putStrLn "already reading a multi-line statement"
          gatherMultiLineInput ln more
        (Nothing, Right (ExecuteFile path)) -> liftIO $ readFile path
        (Just _,  Right (ExecuteFile _))    -> do
          liftIO $ putStrLn "cannot execute a file in the middle of multi-line input"
          gatherMultiLineInput ln more
        (_, Right ReplHelp) -> do
          liftIO $ putStr helpMessage
          gatherMultiLineInput ln more

replAside :: G.Parser ReplAside
replAside =  G.str "#{" *> pure BeginMultiLine
         <|> G.str "#}" *> pure EndMultiLine
         <|> G.str "#run" *> (ExecuteFile <$> G.inlineQuote)
         <|> G.str "#help" *> pure ReplHelp
         <?> "repl side instruction"

replParse :: Int -> String -> ReplIO S.Command
replParse ln input = do
  case parse (G.whole S.command) ("repl line " ++ show ln) input of
    Left err -> throwError $ ParseErr err
    Right sc -> return sc

replPolar :: S.Command -> ReplIO S.Command
replPolar sc = do
  env <- polarSource <$> liftReplState get
  case S.runPolarize (S.semiclosedPolarity $ S.polarizeCmd sc) env of
    (Left err, _) -> throwError $ SourcePolarityErr err
    (Right sp, _) -> do
      let env' = S.cmdPolarityEnv sc
      liftReplState $ modify $ \st -> st{polarSource = env' <> env}
      return sp

replTrans :: S.Command -> ReplIO S.CoreCmd
replTrans cmd = do
  let cmd' = S.endRunGoesTo (S.Var $ S.Implicit S.Join) cmd
  lowered <- runExceptT $ S.desugarCmd cmd'
  case lowered of
    Left err -> throwError $ DesugarErr err
    Right dc -> return dc
{-
replTrans :: S.Statement -> ReplIO S.CoreCmd
replTrans (S.Run t) = do
  lowered <- runExceptT $ S.desugarTerm t
  case lowered of
    Left err -> throwError $ DesugarErr err
    Right t  -> return $ DC.GoJoin t DC.CheckCBV
replTrans stm = do
  lowered <- runExceptT $ S.desugarStmt stm []
  case lowered of
    Left err -> throwError $ DesugarErr err
    Right dc -> return dc
-}

prepExec :: S.CoreCmd -> ReplIO ExecCmd
prepExec c = do
  env <- locals <$> get
  let pols = DC.PolIn $ boundPolarity <$> env
  let c' = eraseTypePole <$> c
  case DC.runPolarize (DC.semiclosedPolarity $ DC.polarizeCmd c') pols of
    (Left err, _) -> throwError $ DualPolarityErr err
    (Right ex, _) -> return ex

eraseTypePole :: S.CorePole -> DC.Dir DC.Strat
eraseTypePole (DC.Check (Internal s)) = DC.Check s
eraseTypePole (DC.Check (External _)) = DC.Infer
eraseTypePole DC.Infer                = DC.Infer
eraseTypePole DC.GoTo                 = DC.GoTo
eraseTypePole DC.ToGo                 = DC.ToGo

boundPolarity :: Bound x i o c a -> Strat
boundPolarity (LetVal _ _) = CBV
boundPolarity (LetFun _ _) = CBN

incrementLineno :: Monad m => ReplT m ()
incrementLineno = liftReplState $ modify inc
  where inc s = s{lineno = succ (lineno s)}

resetLineno :: Monad m => Int -> ReplT m ()
resetLineno n = liftReplState $ modify reset
  where reset s = s{lineno = n}

resetReplPrompt :: Monad m => ReplState -> ReplT m ()
resetReplPrompt rs' = liftReplState $ modify reset
  where reset rs = rs{lineno = lineno rs', polarSource = polarSource rs'}

checkpointSave :: ReplIO ()
checkpointSave = do
  glob <- get
  rs <- liftReplState $ get
  chk <- liftPrompt $ ask
  hst <- liftInput $ getHistory
  liftIO $ writeIORef (execEnv chk) glob
  liftIO $ writeIORef (replState chk) rs
  liftIO $ writeIORef (prevHistory chk) hst
  liftReplState $ modify $ \s -> s{checkpoint = glob}

checkpointLoad :: ReplIO ()
checkpointLoad = do
  glob <- checkpoint <$> liftReplState get
  put glob

checkpointReload :: ReplIO ()
checkpointReload = do
  chk <- checkpointRecover
  checkpointRestore chk

checkpointRecover :: ReplIO Checkpoint
checkpointRecover = liftPrompt ask

checkpointRestore :: Checkpoint -> ReplIO ()
checkpointRestore chk = do
  glob <- liftIO $ readIORef (execEnv chk)
  put glob
  rs <- liftIO $ readIORef (replState chk)
  liftReplState $ put rs
  hst <- liftIO $ readIORef (prevHistory chk)
  liftInput $ putHistory hst

joinId :: ExecId
joinId = Internal DC.Join

captureNextJoin :: ReplIO ()
captureNextJoin = do
  rs <- liftReplState get
  captureNextJoinAs $ Free $ replNextPOp rs

captureNextJoinAs :: ExecCls -> ReplIO ()
captureNextJoinAs j = do
  DC.bindCls joinId DC.CBV j
  return ()



replHandlers :: Extern ExecId S.Literal DC.Strat OpIO Void ReplIO
replHandlers = Extern
  { callExternal = \o c v -> applyOp c o v,
    unhandledPat = \o ps v -> throwError $ RuntimeErr $ UnhandledPattern o ps v,
    expectedData = \o t u -> throwError $ RuntimeErr $ ExpectedData o t u,
    expectedCode = \o t v -> throwError $ RuntimeErr $ ExpectedCode o t v,
    undefinedData = \x -> throwError $ RuntimeErr $ UndefinedData x,
    undefinedCode = \x -> throwError $ RuntimeErr $ UndefinedCode x,
    illdefinedData = \x o c -> throwError $ RuntimeErr $ IlldefinedData x o c,
    illdefinedCode = \x o v -> throwError $ RuntimeErr $ IlldefinedCode x o v }



----------------------
-- Specific PrimOps --
----------------------

unaryNumOp :: String
           -> (Integer -> ExecVal)
           -> (Double -> ExecVal)
           -> OpIO
unaryNumOp name i f = POp { opName = name, applyOp = unaryNumFun name i f }

unaryNumFun :: String
            -> (Integer -> ExecVal)
            -> (Double -> ExecVal)
            -> Strat -> ExecVal -> ReplIO ExecCmd
unaryNumFun name i f o v@(Struc p) = case p of
  (S.Int x :@: MT) :*: C k -> sendToCls o (i x) k
  (S.Flt x :@: MT) :*: C k -> sendToCls o (f x) k
  _                        ->
    throwError $ RuntimeErr $ UnhandledPrimArg name [(AnyNum :@: MT) :*: C()] v

binaryNumOp2 :: String
             -> (Integer -> Integer -> ExecVal)
             -> (Double -> Double -> ExecVal)
             -> OpIO
binaryNumOp2 name i f = POp { opName = name, applyOp = binaryNumFun2 name i f }

binaryNumFun2 :: String
              -> (Integer -> Integer -> ExecVal)
              -> (Double -> Double -> ExecVal)
              -> Strat -> ExecVal -> ReplIO ExecCmd
binaryNumFun2 name i f =
  binaryNumFun name i (\x y -> f x (fromInteger y)) (\x y -> f (fromInteger x) y) f

binaryNumOp :: String
            -> (Integer -> Integer -> ExecVal)
            -> (Double -> Integer -> ExecVal)
            -> (Integer -> Double -> ExecVal)
            -> (Double -> Double -> ExecVal)
            -> OpIO
binaryNumOp name i_i f_i i_f f_f =
  POp { opName = name, applyOp = binaryNumFun name i_i f_i i_f f_f }

binaryNumFun :: String
             -> (Integer -> Integer -> ExecVal)
             -> (Double -> Integer -> ExecVal)
             -> (Integer -> Double -> ExecVal)
             -> (Double -> Double -> ExecVal)
             -> Strat -> ExecVal -> ReplIO ExecCmd
binaryNumFun name i_i f_i i_f f_f o v@(Struc p) = case p of
  (S.Int x :@: MT) :*: ((S.Int y :@: MT) :*: C k)
    -> sendToCls o (i_i x y) k
  (S.Flt x :@: MT) :*: ((S.Flt y :@: MT) :*: C k)
    -> sendToCls o (f_f x y) k
  (S.Flt x :@: MT) :*: ((S.Int y :@: MT) :*: C k)
    -> sendToCls o (f_i x y) k
  (S.Int x :@: MT) :*: ((S.Flt y :@: MT) :*: C k)
    -> sendToCls o (i_f x y) k
  _ -> throwError $ RuntimeErr
     $ UnhandledPrimArg name [(AnyNum :@: MT) :*: ((AnyNum :@: MT) :*: C ())] v

onUnaryLit :: (b -> S.Literal)
           -> (a -> b)
           -> a -> ExecVal
onUnaryLit lit f x = Struc $ (lit $ f x) :@: MT

onUnaryBool :: (a -> Bool)
            -> a -> ExecVal
onUnaryBool f x = if f x then Struc TruePat else Struc FalsePat

onBinaryLit :: (c -> S.Literal)
            -> (a -> b -> c)
            -> a -> b -> ExecVal
onBinaryLit lit f x y = Struc $ (lit $ f x y) :@: MT

onBinaryBool :: (a -> b -> Bool)
             -> a -> b -> ExecVal
onBinaryBool f x y = if f x y
                     then Struc TruePat
                     else Struc FalsePat

equalityOp :: OpIO
equalityOp = POp {
  opName = "==",
  applyOp = \o v@(Struc p) -> case p of
      x :*: (y :*: C k)
        -> sendToCls o (onBinaryBool (==) x y) k
      _ -> throwError $ RuntimeErr $ UnhandledPrimArg "==" [A () :*: (A () :*: C ())] v
  }

notEqualityOp :: OpIO
notEqualityOp = POp {
  opName = "/=",
  applyOp = \o v@(Struc p) -> case p of
      x :*: (y :*: C k)
        -> sendToCls o (onBinaryBool (/=) x y) k
      _ -> throwError $ RuntimeErr $ UnhandledPrimArg "/=" [A () :*: (A () :*: C ())] v
  }

lessThanOp :: OpIO
lessThanOp = binaryNumOp2 "<" (onBinaryBool (<)) (onBinaryBool (<))

greaterThanOp :: OpIO
greaterThanOp = binaryNumOp2 ">" (onBinaryBool (>)) (onBinaryBool (>))

lessEqualOp :: OpIO
lessEqualOp = binaryNumOp2 "=<" (onBinaryBool (<=)) (onBinaryBool (<=))

greaterEqualOp :: OpIO
greaterEqualOp = binaryNumOp2 ">=" (onBinaryBool (>=)) (onBinaryBool (>=))

plusOp :: OpIO
plusOp = binaryNumOp2 "+" (onBinaryLit S.Int (+)) (onBinaryLit S.Flt (+))

minusOp :: OpIO
minusOp = binaryNumOp2 "-" (onBinaryLit S.Int (-)) (onBinaryLit S.Flt (-))

timesOp :: OpIO
timesOp = binaryNumOp2 "*" (onBinaryLit S.Int (*)) (onBinaryLit S.Flt (*))

divideOp :: OpIO
divideOp = POp { opName = "/", applyOp = divideFun }

divideFun o v@(Struc p) = case p of
  (S.Int x :@: MT) :*: ((S.Int y :@: MT) :*: C k)
    | y /= 0
      -> sendToCls o (onBinaryLit S.Int div x y) k
  (S.Flt x :@: MT) :*: ((S.Flt y :@: MT) :*: C k)
    | y /= 0
      -> sendToCls o (onBinaryLit S.Flt (/) x y) k
  (S.Flt x :@: MT) :*: ((S.Int y :@: MT) :*: C k)
    | y /= 0
      -> sendToCls o (onBinaryLit S.Flt (/) x (fromInteger y)) k
  (S.Int x :@: MT) :*: ((S.Flt y :@: MT) :*: C k)
    | y /= 0
      -> sendToCls o (onBinaryLit S.Flt (/) (fromInteger x) y) k
  _ -> throwError $ RuntimeErr $ UnhandledPrimArg "/" expected v
     where expected = [(AnyNum :@: MT) :*: ((CustomPat "nonzero" :@: MT) :*: C ())]


moduloOp :: OpIO
moduloOp = binaryNumOp2 "%" (onBinaryLit S.Int mod) (onBinaryLit S.Flt mod')

exponentOp :: OpIO
exponentOp = binaryNumOp "^"
  (onBinaryLit S.Int (^))
  (onBinaryLit S.Flt (^))
  (onBinaryLit S.Flt (\x y -> fromInteger x ** y))
  (onBinaryLit S.Flt (**))

roundOp :: OpIO
roundOp = unaryNumOp "round" (onUnaryLit S.Int id) (onUnaryLit S.Int round)

ceilingOp :: OpIO
ceilingOp = unaryNumOp "ceiling" (onUnaryLit S.Int id) (onUnaryLit S.Int ceiling)

floorOp :: OpIO
floorOp = unaryNumOp "floor" (onUnaryLit S.Int id) (onUnaryLit S.Int floor)

printOp :: OpIO
printOp = POp {
  opName = "print",
  applyOp = \o v@(Struc p) -> case p of
      (S.Str s :@: MT) :*: C k
        -> do liftIO $ putStrLn $ Txt.unpack s
              sendToCls o (Struc MT) k
      _ -> throwError $ RuntimeErr $ UnhandledPrimArg "print" [(AnyStr :@: MT) :*: C ()] v
  }

pprintOp :: OpIO
pprintOp = POp {
  opName = "pprint",
  applyOp = \o v@(Struc p) -> case p of
      (p :*: C k)
        -> do liftIO $ putDoc $ prettyShortVal (Struc p) <> hardline
              sendToCls o (Struc MT) k
      _ -> throwError $ RuntimeErr $ UnhandledPrimArg "print" [A () :*: C ()] v
  }

runFileOp :: OpIO
runFileOp = POp {
  opName = "run_file",
  applyOp = \_ v@(Struc p) -> case p of
      (S.Str s :@: MT) :*: C k
        -> do let path = Txt.unpack s
              fc <- loadFileForExecution path
              captureNextJoinAs k
              return fc
      _ -> throwError $ RuntimeErr $ UnhandledPrimArg "run_file" [pat] v
        where pat = (CustomPat "_:filepath" :@: MT) :*: C ()
  }

loadFileForExecution :: FilePath -> ReplIO ExecCmd
loadFileForExecution path = do
  txt <- liftIO $ readFile path
  sc <- parseFile path txt
  -- liftIO $ putStrLn "--- Parsed source code ---"
  -- liftIO $ putDoc $ pretty sc <> hardline
  -- liftIO $ putStrLn "--------------------------"
  sp <- filePolar sc
  -- liftIO $ putStrLn "--- Polarized source code ---"
  -- liftIO $ putDoc $ pretty sp <> hardline
  -- liftIO $ putStrLn "-----------------------------"
  let smp = S.simplifyReactsCmd sp
  -- liftIO $ putStrLn "--- Simplified source code ---"
  -- liftIO $ putDoc $ pretty smp <> hardline
  -- liftIO $ putStrLn "------------------------------"
  dc <- fileTrans smp
  -- liftIO $ putStrLn "--- Desugared Dual Core command ---"
  -- liftIO $ putDoc $ pretty dc <> hardline
  -- liftIO $ putStrLn "-----------------------------------"
  ec <- prepExec dc
  -- liftIO $ putStrLn "--- Executable Dual Core command ---"
  -- liftIO $ putDoc $ pretty ec <> hardline
  -- liftIO $ putStrLn "------------------------------------"
  glob <- get
  let fc = runFocus (focusCmd ec) (focusing glob)
  -- liftIO $ putStrLn "--- Focused Dual Core command ---"
  -- liftIO $ putDoc $ pretty fc <> hardline
  -- liftIO $ putStrLn "-----------------------------------"
  return fc

parseFile :: FilePath -> String -> ReplIO S.Command
parseFile path input = do
  case parse (G.whole S.command) path input of
    Left err -> throwError $ ParseErr err
    Right sc -> return sc

filePolar :: S.Command -> ReplIO S.Command
filePolar sc = do
  env <- polarSource <$> liftReplState get
  case S.runPolarize (S.semiclosedPolarity $ S.polarizeCmd sc) env of
    (Left err, _) -> throwError $ SourcePolarityErr err
    (Right sp, _) -> do
      let env' = S.cmdPolarityEnv sc
      liftReplState $ modify $ \st -> st{polarSource = env' <> env}
      return sp

fileTrans :: S.Command -> ReplIO S.CoreCmd
fileTrans cmd = do
  lowered <- runExceptT $ S.desugarCmd cmd
  case lowered of
    Left err -> throwError $ DesugarErr err
    Right dc -> return dc


helpMessage = unlines
  [ "<command>                 execute the given Coo command",
    "#{\\n ...line... \\n#}      enter a command on multiple lines",
    "#run \"<path>\"             read from file <path> and run the command within",
    "#help                     this help message",
    "Ctrl-c                    cancel the currently running command",
    "Ctrl-d                    exit the Coo interpreter" ]
