{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Coo.Source.Desugar where

import Coo.Data.Namespace
import Coo.Source.Syntax
import Coo.Source.Print ()
import qualified Coo.DualCore.Syntax as DC
import qualified Coo.DualCore.Sugar as DC

import qualified Data.Map as M
import qualified Data.Text as Txt
import Data.Bifunctor
import Control.Monad.Reader
import Control.Monad.Except

import Prettyprinter

type CorePole = (DC.Dir DC.Strat, DC.Dir CoreType)
type CoreId = Reserve DC.Label Variable
type CoreParam = CoreId
type CoreSelf = Maybe CoreParam
type CoreLit = Literal
type CorePat = DC.Pat CoreLit CoreParam CoreParam
type CoreCoPat = DC.CoPat CoreLit CoreId CoreId
type CoreType = DC.Type CoreId CoreLit

type CoreValue = DC.Val CoreId CoreLit CorePole CoreId CoreId
type CoreStack = CoreValue

type CoreCmd = DC.Cmd CoreId CoreLit CorePole
type CoreTrm = DC.Trm CoreId CoreLit CorePole
type CoreRsp = DC.Rsp CoreId CoreLit CorePole
type CoreStm = CoreCmd -> CoreCmd

data DesugarError = UnexpectedSelfless Reaction
                  | UnderReaction Command
                  | OverReaction Reaction
                  deriving (Show)

instance Pretty DesugarError where
  pretty (UnexpectedSelfless r) = vsep
    [ pretty "Expected a (recursive) name for the reaction itself in:",
      indent 4 $ pretty $ abridgeReaction r ]
  pretty (UnderReaction c) = vsep
    [ pretty "The reaction has an unhandled remainder before the command:",
      indent 4 $ pretty c ]
  pretty (OverReaction r) = vsep
    [ pretty "The reaction has already consumed everything, but asks for more in:",
      indent 4 $ pretty r ]

type DesugarMonad m = (MonadError DesugarError m)

desugarCmd :: (DesugarMonad m)
           => Command -> m CoreCmd
desugarCmd []      = return DC.GoToJoin
-- desugarCmd [Run t] = desugarStmt (Go t Nothing Nothing) []
desugarCmd (s:c)   = desugarStmt s c

simplifyIdAlias :: CoreCmd -> CoreCmd
simplifyIdAlias (DC.Cut (DC.Var x) _ (DC.Act y c))
  | x == y = c
simplifyIdAlias (DC.Cut (DC.Act x c) _ (DC.Var y))
  | x == y = c
simplifyIdAlias c
  = c

desugarStmt :: (DesugarMonad m)
            => Statement -> Command -> m CoreCmd
desugarStmt s c = simplifyIdAlias <$> desugarStmt' s c

desugarStmt' :: (DesugarMonad m)
             => Statement -> Command -> m CoreCmd
desugarStmt' (Go u a k) _
  | Nothing <- k = DC.Go <$> desugarTerm u <*> pure (desugarAnn a)
  | Just k' <- k = DC.Cut <$> desugarTerm u <*> pure (desugarAnn a) <*> desugarTerm k'
desugarStmt' (Run u) c
  = desugarStmt' (SetMatch (Any (Unbound $ Txt.pack "_")) u Nothing Nothing) c
desugarStmt' (LocalFun d r) c
  = annotateFun <$> desugarFunName d r <*> pure (funType d) <*> desugarReactTm r <*> desugarCmd c
desugarStmt' (SetMatch (Any x) t Nothing Nothing) c
  = DC.LocalVal (desugarParam x) <$> desugarTerm t <*> desugarCmd c
desugarStmt' (SetMatch p t Nothing handle) c
  = do t' <- desugarTerm t
       let r1 = p `Rest` Exec c
       rs' <- desugarReactsTop (r1 `setHandler` handle)
       return $ DC.Cut t' (DC.Check DC.CBV, DC.GoTo) (DC.Cod rs')
desugarStmt' (SetMatch p t (Just (q, u)) handle) c
  = do t' <- desugarTerm t
       let r1 = p `Rest` Guard q u (Exec c)
       rs' <- desugarReactsTop (r1 `setHandler` handle)
       return $ DC.Cut t' (DC.Check DC.CBV, DC.GoTo) (DC.Cod rs')
desugarStmt' (Case t r) c
  = do t' <- desugarTerm t
       rs' <- desugarReactsTop r
       c' <- desugarCmd c
       return $
         DC.AndThen
         (DC.SkipOther $ DC.Cut t' (DC.Check DC.CBV, DC.GoTo) (DC.Cod rs'))
         c'
desugarStmt' (If r) c2
  = do c1 <- desugarGuard r
       let c1' = DC.SkipOther c1
       c2' <- desugarCmd c2
       return $ c1' `DC.AndThen` c2'

setHandler :: Reaction -> Maybe Reaction -> Reaction
r `setHandler` Nothing = r
r `setHandler` Just r' = r `Alt` r'

desugarTerm :: (DesugarMonad m)
            => Term -> m CoreTrm
desugarTerm (Var x)      = return $ DC.Var $ desugarParam x
desugarTerm Nil          = return $ DC.Nil
desugarTerm (Make i v)   = DC.Make i <$> desugarTerm v
desugarTerm (Pair v w)   = DC.Pair <$> desugarTerm v <*> desugarTerm w
desugarTerm (Do rs)      = desugarReactTm rs
desugarTerm (Fn rs)      = desugarTerm (Do rs)
desugarTerm (Obj u)      = DC.Obj <$> desugarTerm u
desugarTerm (App u v)    = DC.App <$> desugarTerm u <*> desugarTerm v
desugarTerm (Dot u i)    = DC.Dot <$> desugarTerm u <*> pure i
desugarTerm (Call u)     = DC.Call <$> desugarTerm u
desugarTerm (Shift p t)  = explicateShift p <$> desugarTerm t
desugarTerm (AsType t c) = DC.AsType <$> desugarTerm t <*> pure (desugarCast c)

explicateShift :: PolarityShift -> CoreTrm -> CoreTrm
explicateShift (PS CBV You) = DC.Call
explicateShift (PS CBN You) = DC.Return
explicateShift (PS CBV Me)  = DC.Thunk
explicateShift (PS CBN Me)  = DC.Force

desugarPat :: Pattern -> CorePat
desugarPat (Any x)        = DC.A $ desugarParam x
desugarPat IsNil          = DC.MT
desugarPat (p `IsPair` q) = desugarPat p DC.:*: desugarPat q
desugarPat (Made i q)     = i DC.:@: desugarPat q
desugarPat (IsObj x)      = DC.C $ desugarParam x

desugarCoPat :: CoPattern -> (CorePat -> CoreCoPat)
desugarCoPat (SelfIs x)     p = desugarSelfParam x DC.:.: p
desugarCoPat (q `CoApp` p') p = desugarCoPat q (desugarPat p' DC.:*: p)
desugarCoPat (q `CoDot` i)  p = desugarCoPat q (i DC.:@: p)

desugarReactsTop :: (DesugarMonad m)
                 => Reaction -> m [CoreRsp]
desugarReactsTop r
  | Just (x, p, c) <- immediateReact r
  = do c' <- desugarCmd c
       return $ [x DC.:.: p DC.:=> c']
desugarReactsTop (r `Alt` rs)
  | Just (x, p, c) <- immediateReact r
  = do c' <- desugarCmd c
       rs' <- desugarReactsTop rs
       return $ (x DC.:.: p DC.:=> c' : rs')
desugarReactsTop Cede
  = return []
desugarReactsTop r
  = do c' <- runReaderT (desugarReactCmd r) id
       return [DC.SelfCoPat DC.HerePat DC.:=> DC.NoOther c']

desugarReacts :: (DesugarMonad m, MonadReader (CorePat -> CorePat) m)
              => Reaction -> m [CoreRsp]
desugarReacts r
  | Just (x, p, c) <- immediateReact r = do
      cxt <- ask
      c' <- contextualizeSelf x (cxt DC.HerePat) <$> desugarCmd c
      return $ [DC.NonRecCoPat p DC.:=> c', DC.Cede]
desugarReacts (r `Alt` rs)
  | Just (x, p, c) <- immediateReact r = do
      cxt <- ask
      c' <- contextualizeSelf x (cxt DC.HerePat) <$> desugarCmd c
      rs' <- desugarReacts rs
      return $ (DC.NonRecCoPat p DC.:=> c' : rs')
desugarReacts r = do
  c' <- desugarReactCmd r
  return [DC.DefaultCoPat DC.:=> c']

immediateReact :: Reaction -> Maybe (CoreSelf, CorePat, Command)
immediateReact r = case r of
  (p `Rest` r)
    | Just c <- irrefutableReact r
      -> Just (Nothing, desugarPat p, c)
  (q `Rec` (p `Rest` r))
    | Just c <- irrefutableReact r
      -> let x' DC.:.: p' = desugarCoPat q (desugarPat p)
         in Just (x', p', c)
  (q `Rec` r)
    | Just c <- irrefutableReact r
      -> let x' DC.:.: p' = desugarCoPat q DC.HerePat
         in Just (x', p', c)
  _ | Just c <- irrefutableReact r
      -> Just (Nothing, DC.HerePat, c)
  _ -> Nothing

irrefutableReact :: Reaction -> Maybe Command
irrefutableReact r = case r of
  Exec c       -> Just c
  Eval t       -> Just [goHere t]
  LetFun d f r -> do
    r' <- irrefutableReact r
    Just $ LocalFun d f : r'
  _            -> Nothing
  where goHere t = Go t (Just $ Annote (Check CBN) ToGo) (Just $ Var $ Implicit Here)

desugarReactCmd :: (DesugarMonad m, MonadReader (CorePat -> CorePat) m)
             => Reaction -> m CoreCmd
desugarReactCmd (Eval t)             = do
  t' <- desugarTerm t
  return $ DC.GoHere t' (DC.Check DC.CBN, DC.ToGo)
desugarReactCmd (Exec c)             = do
  c' <- desugarCmd c
  let t = DC.Act (Internal DC.Context) c'
  return $ DC.GoHere t (DC.Check DC.CBN, DC.ToGo)
desugarReactCmd (p `Rest` r)         = do
  let p' = desugarPat p
  c' <- desugarGuard r
  return
    $ DC.TryHere
    $ (DC.NonRecCoPat p' DC.:=>)
    $ DC.LocalElse (patToDat p')
    $ c'
desugarReactCmd (p `Pop` r)          = do
  let p' = desugarPat p
  c' <- local (. (p' DC.:*:)) $ desugarReactCmd r
  let q = p' DC.:*: DC.HerePat
  return
    $ DC.TryHere
    $ (DC.NonRecCoPat q DC.:=>)
    $ contextualizeOther q
    $ c'
desugarReactCmd (i `Proj` r)         = do
  c' <- local (. (i DC.:@:)) $ desugarReactCmd r
  let q = i DC.:@: DC.HerePat
  return
    $ DC.TryHere
    $ (DC.NonRecCoPat q DC.:=>)
    $ contextualizeOther q
    $ c'
desugarReactCmd (q `Rec` r)   = do
  let x' DC.:.: p' = desugarCoPat q DC.HerePat
  cxt <- ask
  let cxt' = DC.getPat . desugarCoPat q
  c' <- local (. cxt') $ desugarReactCmd r
  return
    $ DC.TryHere
    $ (DC.NonRecCoPat p' DC.:=>)
    $ contextualizeSelf x' (cxt DC.HerePat )
    $ contextualizeOther p'
    $ c'
desugarReactCmd (Guard Nothing t r)  = desugarReactCmd $ Guard (Just TruePat) t r
desugarReactCmd (Guard (Just p) t r) = do
  t' <- desugarTerm t
  let p' = desugarPat p
  c' <- desugarReactCmd r
  return
    $ DC.Cut t' (DC.Check DC.CBV, DC.GoTo)
    $ DC.GuardHere
    $ (DC.NonRecCoPat p' DC.:=>)
    $ c'
desugarReactCmd (LetFun d f r)       = do
  x <- desugarFunName d f
  t <- desugarReactTm f
  c <- desugarReactCmd r
  return $ annotateFun x (funType d) t c
desugarReactCmd Cede                 = return DC.FallOut
desugarReactCmd (r1 `Alt` r2)        = do
  c1' <- desugarReactCmd r1
  r2' <- desugarReacts r2
  let t2 = DC.Cod r2'
  return
    $ DC.LocalAlt t2
    $ c1'
desugarReactCmd (Else x r)           = do
  c' <- desugarReactCmd r
  return
    $ DC.LocalAct (desugarParam x) DC.OtherVar
    $ c'

contextualizeSelf :: CoreSelf -> CorePat -> CoreCmd -> CoreCmd
contextualizeSelf Nothing     _          = id
contextualizeSelf (Just name) DC.HerePat = DC.LocalAct name DC.SelfVar
contextualizeSelf (Just name) cxt        = DC.LocalSelf name (patToDat cxt)

contextualizeOther :: CorePat -> CoreCmd -> CoreCmd
contextualizeOther DC.HerePat c = c
contextualizeOther cxt        c = DC.LocalOther (patToDat cxt) c

{-
renameSelf :: CoreId -> CoreCmd -> CoreCmd
renameSelf (Internal DC.Self) c = c
renameSelf name               c = DC.Cut DC.SelfVar DC.InferCBN (DC.Act name c)
-}

desugarGuard :: (DesugarMonad m)
             => Reaction -> m CoreCmd
desugarGuard (Exec c)             = desugarCmd c
desugarGuard (Eval t)             = desugarGuard $ Exec [Go t Nothing Nothing]
desugarGuard (Guard Nothing t r)  = desugarGuard $ Guard (Just TruePat) t r
desugarGuard (Guard (Just p) t r) = do
  t' <- desugarTerm t
  let p' = desugarPat p
  c' <- desugarGuard r
  let guarded = DC.Guard $ DC.NonRecCoPat p' DC.:=> c'
  return $ DC.Cut t' (DC.Check DC.CBV, DC.GoTo) guarded
desugarGuard (LetFun d f r)       = do
  x <- desugarFunName d f
  t <- desugarReactTm f
  c <- desugarGuard r
  return $ annotateFun x (funType d) t c
desugarGuard Cede                 = return DC.FallThrough
desugarGuard (r1 `Alt` r2)        = do
  c1 <- desugarGuard r1
  c2 <- desugarGuard r2
  return $ DC.LocalAlt (DC.Abort c2) c1
desugarGuard r                    = throwError $ OverReaction r

patToDat :: DC.Pat i x x -> DC.Trm x i o
patToDat p = DC.Dat $ DC.Struc $ first DC.Free p

desugarReactTm :: (DesugarMonad m)
               => Reaction -> m CoreTrm
desugarReactTm (Eval t)
  = desugarTerm t
desugarReactTm (Exec c)
  = DC.Act (Internal DC.Context) <$> desugarCmd c
desugarReactTm (Any x `Rest` Exec c)
  = DC.Act (desugarParam x) <$> desugarCmd c
desugarReactTm r
  = DC.Cod <$> runReaderT (desugarReactsTop r) DC.HerePat


desugarCast :: TypeCast -> CorePole
desugarCast (PrefixType a)  = desugarAnn $ Just a
desugarCast (PostfixType a) = desugarAnn $ Just a

desugarAnn :: Maybe Annotation -> CorePole
desugarAnn (Just (Annote s t)) = (desugarDir $ desugarStrat <$> s,
                                  desugarDir $ desugarType  <$> t)
desugarAnn Nothing             = (DC.Infer, DC.Infer)

desugarDir :: Dir o -> DC.Dir o
desugarDir Infer     = DC.Infer
desugarDir GoTo      = DC.GoTo
desugarDir ToGo      = DC.ToGo
desugarDir (Check x) = DC.Check x

desugarStrat :: Strat -> DC.Strat
desugarStrat CBV = DC.CBV
desugarStrat CBN = DC.CBN

desugarType :: Type -> CoreType
desugarType (VarTy x)       = DC.VarTy $ External x
-- desugarType (RecTy x t)     = DC.RecTy (External x) $ desugarType t
desugarType UnitTy          = DC.UnitTy
desugarType (s `PairTy` t)  = desugarType s `DC.PairTy` desugarType t
desugarType (s `ArrowTy` t) = desugarType s `DC.PairTy` desugarType t
desugarType (TagTy xts)     = DC.TagTy $ M.fromList [ (x, desugarType t) | (x, t) <- xts ]
desugarType (ObjTy t)       = DC.ObjTy $ desugarType t

desugarParam :: Parameter -> CoreParam
desugarParam (Bound x)    = External x
desugarParam (Implicit x) = Internal (desugarLabel x)
desugarParam (Unbound _)  = Internal DC.Blank

desugarSelfParam :: Parameter -> CoreSelf
desugarSelfParam (Bound x)    = Just $ External x
desugarSelfParam (Implicit x) = Just $ Internal (desugarLabel x)
desugarSelfParam (Unbound _)  = Nothing

desugarLabel :: Label -> DC.Label
desugarLabel Here      = DC.Here
desugarLabel Join      = DC.Join
desugarLabel Self      = DC.Self
desugarLabel Other     = DC.Other
desugarLabel Context   = DC.Context
desugarLabel Unmatched = DC.Unmatched

desugarFunName d r
  | Just x <- extractFunName d r = return $ desugarParam x
  | otherwise                    = throwError $ UnexpectedSelfless r

desugarSelfName :: MonadError DesugarError m => Reaction -> m CoreParam
desugarSelfName r
  | Just x <- extractSelfName r = return $ desugarParam x
  | otherwise                   = throwError $ UnexpectedSelfless r

funType (_, t) = desugarType <$> t

annotateFun x Nothing  = DC.LocalFun x
annotateFun x (Just t) = DC.LocalFunAs x (DC.Check t)
