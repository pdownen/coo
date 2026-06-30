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
import qualified Coo.Source.TypeCheck as S
import qualified Coo.Source.Simplify as S
import qualified Coo.Source.Desugar as S
import Coo.Source.Print ()

import Coo.DualCore.Syntax as DC
import Coo.DualCore.Sugar as DC
import Coo.DualCore.Focus as DC
import Coo.DualCore.Polarity as DC hiding (UnboundConstraints)
import Coo.DualCore.TypeCheck as DC
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

type UntypedCmd = DC.Cmd ExecId S.Literal (DC.UnelabPole ExecId S.Literal)
type TypedCmd = DC.Cmd ExecId S.Literal (DC.ElabPole ExecId S.Literal)

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
  = POp { opName  :: Txt.Text,
          applyOp :: Strat -> Val x i o (PrimOp x i o a m) a
                  -> m (Cmd x i o) }

instance Eq (PrimOp x i o a m) where
  f == g = opName f == opName g

instance Show (PrimOp x i o a m) where
  show op = "<#" ++ Txt.unpack (opName op) ++ "#>"

instance Pretty (PrimOp x i o a m) where
  pretty = viaShow

type POp m = PrimOp ExecId S.Literal DC.Strat Void (ReplT m)

type OpIO = POp PromptIO

type Glob m = DC.Global ExecId S.Literal DC.Strat (POp m) Void (ReplT m)

type GlobIO = Glob PromptIO

data ReplState = RS { lineno      :: Int,
                      polarSource :: S.PolInEnv,
                      typeSource  :: S.TyInEnv,
                      typeCore    :: DC.TyInEnv ExecId S.Literal,
                      checkpoint  :: GlobIO,
                      replOptions :: ReplOptions }

data ReplOptions = RO { typeOption :: TypeCheckingOption,
                        batchOption :: Bool,
                        stopAfterTypes :: Bool }
  deriving (Show, Eq)

data ReplError
  = ParseErr (ParseErrorBundle String Void)
  | SourcePolarityErr S.PolarityError
  | SourceTypeErr S.TypeError
  | DesugarErr S.DesugarError
  | DualPolarityErr (DC.PolarityError ExecId S.Literal)
  | DualTypeErr (DC.TypeError ExecId S.Literal)
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
  pretty (SourceTypeErr err) = hsep
    [ pretty "Type Error:",
      pretty err ]
  pretty (DualPolarityErr err) = hsep
    [ pretty "Polarity Error (internal):",
      pretty err ]
  pretty (DualTypeErr err) = hsep
    [ pretty "Type Error (internal):",
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


makeSourceTyEnv table = M.fromList table

bindLocalOp pop = (External $ opName pop,
                   LetFun CBN $ Free pop)

makeLocalEnv table = M.fromList [ bindLocalOp pop | (pop, _) <- table ]

initEnv :: Env ExecId S.Literal DC.Strat OpIO Void
initEnv = makeLocalEnv primOpTable

bindPolarityOp pop = (S.Bound $ opName pop, S.CBN)

makePolarityEnv table = S.PolIn $ M.fromList [ bindPolarityOp pop | (pop, _) <- table ]

initPolarity :: S.PolInEnv
initPolarity = makePolarityEnv primOpTable

makeInitGlob :: [(OpIO, S.Type)] -> GlobIO
makeInitGlob primOps = DC.Global { DC.extern = replHandlers,
                                   DC.locals = makeLocalEnv primOps,
                                   DC.focusing = initFocus }

initGlob :: GlobIO
initGlob = makeInitGlob primOpTable

initFocus :: FocusSettings Strat ExecId Int
initFocus = DC.FocAs { DC.fociNote = DC.stratFoci CBV,
                       DC.tempZero = 0,
                       DC.nameTemp = Internal . DC.Temp,
                       DC.nameHere = Internal DC.It }

makePrimTypeCxt :: [S.PrimType] -> M.Map S.Variable S.PrimType
makePrimTypeCxt table = M.fromList [ (primTyName t, t) | t <- table ]

makeLocalTypeCxt :: [(OpIO, S.Type)] -> M.Map S.Parameter S.ElabPole
makeLocalTypeCxt table = M.fromList
  [ (S.Bound $ opName x, S.CBN S.::: t)
  | (x, t) <- table ]

makeSourceTyInEnv :: [S.PrimType] -> [(OpIO, S.Type)] -> S.TyInEnv
makeSourceTyInEnv primTys primOps =
  S.TyIn (makePrimTypeCxt primTys) (makeLocalTypeCxt primOps)

desugarTyInEnv :: S.TyInEnv -> DC.TyInEnv S.CoreId S.Literal
desugarTyInEnv (S.TyIn ptys vars) = DC.TyIn ptys' vars'
  where ptys' = M.fromList [ (External x, pty)
                           | (x, pty) <- M.toList ptys ]
        vars' = M.fromList [ (S.desugarParam x,
                              S.desugarStrat s DC.::: S.desugarType t)
                           | (x, s S.::: t) <- M.toList vars ]

defaultOptions :: ReplOptions
defaultOptions = RO { typeOption  = IgnoreTypes,
                      batchOption = False,
                      stopAfterTypes = False }

makeInitRS :: [S.PrimType] -> [(OpIO, S.Type)] -> ReplState
makeInitRS primTys primOps =
  RS { lineno = 0,
       polarSource = makePolarityEnv primOps,
       typeSource  = tyInEnv,
       typeCore    = desugarTyInEnv tyInEnv,
       checkpoint  = makeInitGlob primOps,
       replOptions = defaultOptions }
  where tyInEnv = makeSourceTyInEnv primTys primOps

initRS :: ReplState
initRS = makeInitRS primTyTable primOpTable

initCmd :: ExecCmd
initCmd = DC.Cut DC.NilVal DC.CBV (DC.Var (Internal DC.Join))

batchCmd :: FilePath -> ExecCmd
batchCmd path = DC.Cut (DC.Lit $ S.Str $ Txt.pack path) DC.CBV (DC.Var (Internal DC.Join))

runScript :: ReplOptions -> FilePath -> IO ()
runScript opts path = do
  result <- runPromptIOinit $ runReplIOinit $ do
    liftReplState $ modify $ \rs -> rs{replOptions = opts}
    captureNextJoin
    cmd <- loadFileForExecution path
    DC.loop cmd
  case result of
    (Right (), _) -> return ()
    (Left err, _) -> putDoc $ pretty err <> hardline

replTop :: IO r
replTop = replTopWith defaultOptions initCmd

replTopWith :: ReplOptions -> ExecCmd -> IO r
replTopWith opt cmd = do
  globr <- newIORef initGlob
  rsr <- newIORef initRS{replOptions = opt}
  hsr <- newIORef emptyHistory
  let chk = Save globr rsr hsr
  runPromptIO chk $ runReplIOinit $ replStart cmd
  forever (runPromptIO chk $ runReplIOinit $ replRestart cmd)

replStart :: ExecCmd -> ReplIO ()
replStart cmd = do
  captureNextJoin
  checkpointSave
  overInput withInterrupt $ replLoop cmd

replRestart :: ExecCmd -> ReplIO ()
replRestart cmd = do
  checkpointReload
  overInput withInterrupt $ replLoop cmd

replLoop :: ExecCmd -> ReplIO ()
replLoop cmd =
  handleInterrupt
  (liftIO $ putStrLn "...")
  (DC.loop cmd -- DC.loopBy printStep cmd
   `catchError`
   \err -> do
     liftIO $ putDoc $ pretty err <> hardline
     batch <- batchOption . replOptions <$> liftReplState get
     if batch
       then liftIO exitFailure
       else do checkpointLoad
               replLoop cmd)

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
replNextPOp rs = POp { opName = Txt.pack $ "repl#" ++ show (lineno rs),
                       applyOp = \_ -> replNext rs }

replNext :: ReplState -> ExecVal -> ReplIO ExecCmd
replNext rs v = do
  checkpointSave
  printVal v
  nextCommand rs

printVal :: ExecVal -> ReplIO ()
printVal (Struc MT) = return ()
printVal v          = liftIO $ putDoc $ pretty "=" <+> prettyShortVal v <> hardline

nextCommand :: ReplState -> ReplIO ExecCmd
nextCommand rs = do
  resetReplPrompt rs
  input <- gatherInput (lineno rs)
  processCommand ("repl line " ++ show (lineno rs)) input

processCommand :: String -> String -> ReplIO ExecCmd
processCommand place input = do
  rs <- liftReplState get
  sc <- replParse place input
  -- liftIO $ putStrLn "--- Parsed source code ---"
  -- liftIO $ putDoc $ pretty sc <> hardline
  -- liftIO $ putStrLn "--------------------------"
  sp <- replPolar sc
  -- liftIO $ putStrLn "--- Polarized source code ---"
  -- liftIO $ putDoc $ pretty sp <> hardline
  -- liftIO $ putStrLn "-----------------------------"
  st <- typeCheckSource (typeOption $ replOptions rs) sp
  -- liftIO $ putStrLn "--- Typed source code ---"
  -- liftIO $ putDoc $ pretty st <> hardline
  -- liftIO $ putStrLn "-------------------------"
  smp <- replSimplify st
  -- liftIO $ putStrLn "--- Simplified source code ---"
  -- liftIO $ putDoc $ pretty smp <> hardline
  -- liftIO $ putStrLn "------------------------------"
  dc <- replTrans smp
  -- liftIO $ putStrLn "--- Desugared Dual Core command ---"
  -- liftIO $ putDoc $ pretty dc <> hardline
  -- liftIO $ putStrLn "-----------------------------------"
  dt <- typeCheckCore (typeOption $ replOptions rs) dc
  -- liftIO $ putStrLn "--- Typed Dual Core command ---"
  -- liftIO $ putDoc $ pretty (preCheckCore dt) <> hardline
  -- liftIO $ putStrLn "-------------------------------"
  afterTypeCheck
  ec <- prepExec dt
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

data ReplAside = BeginMultiLine
               | EndMultiLine
               | ExecuteFile String
               | CheckTypeOfExpr String
               | SetTypeChecker TypeCheckingOption
               | ReplHelp
  deriving (Show, Eq)

data TypeCheckingOption = IgnoreTypes | TypeWarnings | TypeErrors
  deriving (Show, Eq, Ord, Enum, Bounded)

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
      case (more, parse (G.perfect replAside) ("repl line " ++ show ln) txt) of
        (Nothing,   Left _) -> return txt
        (Just prev, Left _) -> gatherMultiLineInput ln (Just $ txt:prev)
        (Just prev, Right EndMultiLine) -> return $ unlines $ reverse prev
        (Nothing,   Right EndMultiLine) -> do
          liftIO $ putStrLn "# not currently reading a multi-line statement"
          gatherMultiLineInput ln more
        (Nothing, Right BeginMultiLine) -> gatherMultiLineInput ln (Just [])
        (Just _,  Right BeginMultiLine) -> do
          liftIO $ putStrLn "# already reading a multi-line statement"
          gatherMultiLineInput ln more
        (Nothing, Right (ExecuteFile path)) -> liftIO $ readFile path
        (Just _,  Right (ExecuteFile _))    -> do
          liftIO $ putStrLn "# cannot execute a file in the middle of multi-line input"
          gatherMultiLineInput ln more
        (_, Right (CheckTypeOfExpr str)) -> do
          checkTypeOfExpr str
          gatherMultiLineInput ln more
        (Nothing, Right (SetTypeChecker mode)) -> do
          liftReplState $ modify $ \rs ->
            rs{replOptions = (replOptions rs){typeOption = mode}}
          let msg = case mode of
                      IgnoreTypes -> "# now ignoring static types"
                      TypeWarnings -> "# now warning about static type errors"
                      TypeErrors -> "# now enforcing static types"
          liftIO $ putStrLn msg
          return ""
        (Just _, Right (SetTypeChecker _)) -> do
          liftIO $ putStrLn "# cannot change typing mode in the middle of multi-line input"
          gatherMultiLineInput ln more
        (_, Right ReplHelp) -> do
          liftIO $ putStr helpMessage
          gatherMultiLineInput ln more

replAside :: G.Parser ReplAside
replAside =  G.exact "#" *> replSideInstruction
         <?> "repl aside"

replSideInstruction :: G.Parser ReplAside
replSideInstruction =  G.exact "{" *> pure BeginMultiLine
                   <|> G.exact "}" *> pure EndMultiLine
                   <|> G.exact "run" *> (ExecuteFile <$> G.inlineQuote)
                   <|> G.exact "help" *> pure ReplHelp
                   <|> G.exact "type" *> (SetTypeChecker <$> typeCheckingOption)
                   <|> G.exact "check" *> (CheckTypeOfExpr <$> G.anything)
                   <?> "repl side instruction (try asking for #!help)"

typeCheckingOption :: G.Parser TypeCheckingOption
typeCheckingOption =  G.exact "ignore" *> pure IgnoreTypes
                  <|> G.exact "warn" *> pure TypeWarnings
                  <|> G.exact "error" *> pure TypeErrors

checkTypeOfExpr :: String -> ReplIO (Maybe S.ElabPole)
checkTypeOfExpr input = do
  case parse (G.whole S.term) "type checking" input of
    Left err -> do
      liftIO $ putDoc $ pretty (ParseErr err) <> hardline
      return Nothing
    Right t -> do
      rs <- liftReplState get
      let ps = polarSource rs
      case S.runPolarize (S.autoPolarizeTerm t) ps of
        (Left err, env) ->
          processPolarResult rs (Left err, env)
        (Right (Just t'), env) ->
          processPolarResult rs (Right t', env)
        (Right Nothing, _) -> do
          liftIO $ putStrLn "Interpreted as a value"
          liftIO $ putStrLn "----------------------"
          processPolarResult rs $ S.runPolarize (S.polarizeTerm S.CBV t) ps
          liftIO $ putStrLn "========================================"
          liftIO $ putStrLn "Interpreted as a function"
          liftIO $ putStrLn "-------------------------"
          processPolarResult rs $ S.runPolarize (S.polarizeTerm S.CBN t) ps
  where processPolarResult rs (Right t', _) = do
          processTypeResult rs $ S.runTypeCheck (S.inferTypeTerm t') (typeSource rs)
        processPolarResult _  (Left err, S.PolOut env) = do
          liftIO $ putDoc $ pretty (SourcePolarityErr err) <> hardline
          liftIO $ putStrLn "----------------------------------------"
          if M.null env
            then return ()
            else liftIO $ putDoc $ vsep [ pretty "Constraints:",
                                          indent 4 (pretty $ S.PolOut env),
                                          mempty ]
          return Nothing

        processTypeResult _ (Right (t', a), env) = do
          liftIO $ putDoc $ vsep [ pretty t',
                                   colon <+> pretty a,
                                   mempty ]
          printConstraints env
          return $ Just a
        processTypeResult _ (Left err, env) = do
          liftIO $ putDoc $ pretty (SourceTypeErr err) <> hardline
          liftIO $ putStrLn "----------------------------------------"
          printConstraints env
          return Nothing

        printConstraints (S.TyOut env)
          | M.null env = return ()
          | otherwise  = do
              liftIO $ putDoc $ vsep [ pretty "Constraints:",
                                       indent 4 (pretty $ S.TyOut env),
                                       mempty ]

replParse :: (MonadError ReplError m) => String -> String -> m S.Command
replParse place input = do
  case parse (G.whole S.command) place input of
    Left err -> throwError $ ParseErr err
    Right sc -> return sc

replPolar :: (Monad m) => S.Command -> ReplT m S.Command
replPolar sc = do
  env <- polarSource <$> liftReplState get
  case S.runPolarize (S.semiclosedPolarity $ S.polarizeCmd sc) env of
    (Left err, _) -> throwError $ SourcePolarityErr err
    (Right sp, _) -> do
      let env' = S.cmdPolarityEnv sc
      liftReplState $ modify $ \rs -> rs{polarSource = env' <> env}
      return sp

typeCheckSource :: (MonadIO m) => TypeCheckingOption -> S.Command -> ReplT m S.Command
typeCheckSource IgnoreTypes c = return c
typeCheckSource opt c = do
  rs <- liftReplState get
  case S.runTypeCheck (S.semiclosedTypeCheck $ S.elaborateStms c) (typeSource rs) of
    (Right (c', env'), _) -> do
      liftReplState $ modify $ \rs' ->
        rs'{ typeSource = env' <> typeSource rs',
             typeCore = desugarTyInEnv env' <> typeCore rs' }
      return c'
    (Left err, _) -> do
      let tyerr = SourceTypeErr err
      case opt of
        TypeWarnings -> do liftIO $ putDoc $ pretty tyerr <> hardline
                           liftIO $ putStrLn "----------------------------------------"
                           return c
        TypeErrors   -> throwError tyerr

replSimplify :: (Monad m) => S.Command -> ReplT m S.Command
replSimplify cmd = do
  opt <- typeOption . replOptions <$> liftReplState get
  case opt of
    IgnoreTypes -> return $ S.simplifyReactsCmd cmd
    _           -> return cmd

isJoinConstraint env = M.keys env == [joinId]

typeCheckCore :: (MonadIO m)
              => TypeCheckingOption
              -> S.CoreCmd
              -> ReplT m S.CoreCmd
typeCheckCore IgnoreTypes c = return c
typeCheckCore opt c = do
  env <- typeCore <$> liftReplState get
  case DC.runTypeCheck (DC.elaborateCmd $ preCheckCore c) env of
    (Right c', TyOut env)
      | M.null env          -> return $ postCheckCore c'
      | isJoinConstraint env, Just (_ ::? Typed t) <- M.lookup joinId env -> do
          case t of
            UnitTy -> return ()
            _      -> liftIO $ putDoc $ pretty ":" <+> pretty t <> hardline
          return $ postCheckCore c'
      | otherwise           -> handleTypeErr $ DualTypeErr $ UnboundConstraints $ TyOut env
    (Left err, _)           -> handleTypeErr $ DualTypeErr err
  where handleTypeErr err = case opt of
          TypeWarnings -> do liftIO $ putDoc $ pretty err <> hardline
                             liftIO $ putStrLn "----------------------------------------"
                             return c
          TypeErrors   -> throwError err

preCheckCore :: S.CoreCmd -> UntypedCmd
preCheckCore = fmap merge
  where merge (Check s, Check a) = Check (s ::: a)
        merge (GoTo, _) = GoTo
        merge (_, GoTo) = GoTo
        merge (ToGo, _) = ToGo
        merge (_, ToGo) = ToGo
        merge _         = Infer

postCheckCore :: TypedCmd -> S.CoreCmd
postCheckCore = fmap split
  where split (s ::: a) = (Check s, Check a)

afterTypeCheck :: (MonadIO m) => ReplT m ()
afterTypeCheck = do
  dryRun <- stopAfterTypes . replOptions <$> liftReplState get
  if dryRun
    then liftIO exitSuccess
    else return ()

continueCmd :: S.Command -> S.Command
continueCmd = S.endRunGoesTo (Just inferCBVFromTerm) (Just nextCont)
  where inferCBVFromTerm = S.Annote (S.Check S.CBV) S.GoTo
        nextCont = S.Var $ S.Implicit S.Join

replTrans :: (MonadError ReplError m) => S.Command -> m S.CoreCmd
replTrans cmd = do
  lowered <- runExceptT $ S.desugarCmd $ continueCmd cmd
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

prepExec :: (Monad m) => S.CoreCmd -> ReplT m ExecCmd
prepExec c = do
  env <- locals <$> get
  let pols = DC.PolIn $ boundPolarity <$> env
  let c' = eraseTypePole <$> c
  case DC.runPolarize (DC.semiclosedPolarity $ DC.polarizeCmd c') pols of
    (Left err, _) -> throwError $ DualPolarityErr err
    (Right ex, _) -> return ex

eraseTypePole :: S.CorePole -> DC.Dir DC.Strat
eraseTypePole = fst

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
  let nextJoin
        | batchOption (replOptions rs) = exitProgPOp
        | otherwise                    = replNextPOp rs
  captureNextJoinAs $ Free nextJoin

captureNextJoinAs :: (MonadState (Global ExecId i Strat c a f) m)
                  => Cls ExecId i Strat c a -> m ()
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

-------------------------
-- Specific Primitives --
-------------------------

primTyTable :: [S.PrimType]
primTyTable = [ intPrimTy, floatPrimTy, stringPrimTy, boolPrimTy ]

intPrimTy :: S.PrimType
intPrimTy = PrimTy { primTyName   = S.IntTyName,
                     checkPrimPat = anyInt }
  where anyInt (S.Int n :@: MT)  = Just (S.Int n :@: MT)
        anyInt (S.Int n :@: A p) = Just (S.Int n :@: A (UnitTy, p))
        anyInt _                 = Nothing

floatPrimTy :: S.PrimType
floatPrimTy = PrimTy { primTyName   = S.FloatTyName,
                       checkPrimPat = anyFlt }
  where anyFlt (S.Flt x :@: MT)  = Just (S.Flt x :@: MT)
        anyFlt (S.Flt x :@: A p) = Just (S.Flt x :@: A (UnitTy, p))
        anyFlt (S.Int n :@: MT)  = Just (S.Flt (fromInteger n) :@: MT)
        anyFlt (S.Int n :@: A p) = Just (S.Flt (fromInteger n) :@: A (UnitTy, p))
        anyFlt _                 = Nothing

stringPrimTy :: S.PrimType
stringPrimTy = PrimTy { primTyName   = S.StringTyName,
                        checkPrimPat = anyStr }
  where anyStr (S.Str s :@: MT)  = Just (S.Str s :@: MT)
        anyStr (S.Str s :@: A p) = Just (S.Str s :@: A (UnitTy, p))
        anyStr _                 = Nothing

boolPrimTy :: S.PrimType
boolPrimTy = PrimTy { primTyName   = S.BoolTyName,
                      checkPrimPat = trueOrFalse }
  where trueOrFalse (i :@: MT)
          | i == S.TrueTag || i == S.FalseTag = Just (i :@: MT)
        trueOrFalse (i :@: A p)
          | i == S.TrueTag || i == S.FalseTag = Just (i :@: A (UnitTy, p))
        trueOrFalse _                         = Nothing


primOpTable :: [(OpIO, S.Type)]
primOpTable = [ (equalityOp,     binaryIntCompareTy),
                (notEqualityOp,  binaryIntCompareTy),
                (lessThanOp,     binaryIntCompareTy),
                (greaterThanOp,  binaryIntCompareTy),
                (lessEqualOp,    binaryIntCompareTy),
                (greaterEqualOp, binaryIntCompareTy),
                
                (plusOp,     binaryIntOpTy),
                (minusOp,    binaryIntOpTy),
                (timesOp,    binaryIntOpTy),
                (divideOp,   binaryIntOpTy),
                (moduloOp,   binaryIntOpTy),
                (exponentOp, binaryIntOpTy),

                (roundOp,   S.FloatTy `S.ArrowTy` S.ObjTy S.IntTy),
                (ceilingOp, S.FloatTy `S.ArrowTy` S.ObjTy S.IntTy),
                (floorOp,   S.FloatTy `S.ArrowTy` S.ObjTy S.IntTy),

                (printOp,  S.StringTy `S.ArrowTy` S.ObjTy S.UnitTy),
                (pprintOp, S.IntTy `S.ArrowTy` S.ObjTy S.UnitTy),

                (runFileOp, S.StringTy `S.ArrowTy` S.ObjTy S.UnitTy) ]

binaryFunTy a b c = a `S.ArrowTy` (b `S.ArrowTy` S.ObjTy c)
binaryIntOpTy = binaryFunTy S.IntTy S.IntTy S.IntTy
binaryFltOpTy = binaryFunTy S.FloatTy S.FloatTy S.FloatTy
binaryStrOpTy = binaryFunTy S.StringTy S.StringTy S.StringTy
binaryIntCompareTy = binaryFunTy S.IntTy S.IntTy S.BoolTy


unaryNumOp :: String
           -> (Integer -> ExecVal)
           -> (Double -> ExecVal)
           -> OpIO
unaryNumOp name i f = POp { opName = Txt.pack name, applyOp = unaryNumFun name i f }

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
binaryNumOp2 name i f = POp { opName = Txt.pack name, applyOp = binaryNumFun2 name i f }

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
  POp { opName = Txt.pack name, applyOp = binaryNumFun name i_i f_i i_f f_f }

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
  opName = Txt.pack "==",
  applyOp = \o v@(Struc p) -> case p of
      x :*: (y :*: C k)
        -> sendToCls o (onBinaryBool (==) x y) k
      _ -> throwError $ RuntimeErr $ UnhandledPrimArg "==" [A () :*: (A () :*: C ())] v
  }

notEqualityOp :: OpIO
notEqualityOp = POp {
  opName = Txt.pack "/=",
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
divideOp = POp { opName = Txt.pack "/", applyOp = divideFun }

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
  opName = Txt.pack "print",
  applyOp = \o v@(Struc p) -> case p of
      (S.Str s :@: MT) :*: C k
        -> do liftIO $ putStrLn $ Txt.unpack s
              sendToCls o (Struc MT) k
      _ -> throwError $ RuntimeErr $ UnhandledPrimArg "print" [(AnyStr :@: MT) :*: C ()] v
  }

pprintOp :: OpIO
pprintOp = POp {
  opName = Txt.pack "pprint",
  applyOp = \o v@(Struc p) -> case p of
      (p :*: C k)
        -> do liftIO $ putDoc $ prettyShortVal (Struc p) <> hardline
              sendToCls o (Struc MT) k
      _ -> throwError $ RuntimeErr $ UnhandledPrimArg "print" [A () :*: C ()] v
  }

exitProgPOp :: OpIO
exitProgPOp = POp { opName = Txt.pack "exit",
                    applyOp = \_ _ -> liftIO exitSuccess }

runFileOp :: OpIO
runFileOp = POp {
  opName = Txt.pack "run_file",
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
  processCommand path txt
{-
loadFileForExecution path = do
  typeOpt <- typeOption . replOptions <$> liftReplState get
  txt <- liftIO $ readFile path
  sc <- parseFile path txt
  -- liftIO $ putStrLn "--- Parsed source code ---"
  -- liftIO $ putDoc $ pretty sc <> hardline
  -- liftIO $ putStrLn "--------------------------"
  sp <- filePolar sc
  -- liftIO $ putStrLn "--- Polarized source code ---"
  -- liftIO $ putDoc $ pretty sp <> hardline
  -- liftIO $ putStrLn "-----------------------------"
  st <- typeCheckSource typeOpt sp
  -- liftIO $ putStrLn "--- Typed source code ---"
  -- liftIO $ putDoc $ pretty st <> hardline
  -- liftIO $ putStrLn "-------------------------"
  smp <- replSimplify st
  -- liftIO $ putStrLn "--- Simplified source code ---"
  -- liftIO $ putDoc $ pretty smp <> hardline
  -- liftIO $ putStrLn "------------------------------"
  dc <- fileTrans smp
  -- liftIO $ putStrLn "--- Desugared Dual Core command ---"
  -- liftIO $ putDoc $ pretty dc <> hardline
  -- liftIO $ putStrLn "-----------------------------------"
  dt <- typeCheckCore typeOpt dc
  -- liftIO $ putStrLn "--- Typed Dual Core command ---"
  -- liftIO $ putDoc $ pretty (preCheckCore dt) <> hardline
  -- liftIO $ putStrLn "-------------------------------"
  ec <- prepExec dt
  -- liftIO $ putStrLn "--- Executable Dual Core command ---"
  -- liftIO $ putDoc $ pretty ec <> hardline
  -- liftIO $ putStrLn "------------------------------------"
  glob <- get
  let fc = runFocus (focusCmd ec) (focusing glob)
  -- liftIO $ putStrLn "--- Focused Dual Core command ---"
  -- liftIO $ putDoc $ pretty fc <> hardline
  -- liftIO $ putStrLn "-----------------------------------"
  return fc

parseFile :: (MonadError ReplError m)
          => FilePath -> String -> m S.Command
parseFile path input = do
  case parse (G.whole S.command) path input of
    Left err -> throwError $ ParseErr err
    Right sc -> return sc

filePolar :: (Monad m) => S.Command -> ReplT m S.Command
filePolar sc = do
  env <- polarSource <$> liftReplState get
  case S.runPolarize (S.semiclosedPolarity $ S.polarizeCmd sc) env of
    (Left err, _) -> throwError $ SourcePolarityErr err
    (Right sp, _) -> do
      let env' = S.cmdPolarityEnv sc
      liftReplState $ modify $ \st -> st{polarSource = env' <> env}
      return sp

fileTrans :: (MonadError ReplError m)
          => S.Command -> m S.CoreCmd
fileTrans cmd = do
  lowered <- runExceptT $ S.desugarCmd cmd
  case lowered of
    Left err -> throwError $ DesugarErr err
    Right dc -> return dc
-}


helpMessage = unlines
  [ "<command>                   execute the given Coo command",
    "#{\\n ...line... \\n#}        enter a command on multiple lines",
    "#run \"<path>\"               read from file <path> and run the command within",
    "#check <expression>         check the type of the given expression",
    "#type ignore|warn|error     set type checking mode",
    "#help                       this help message",
    "Ctrl-c                      cancel the currently running command",
    "Ctrl-d                      exit the Coo interpreter" ]
