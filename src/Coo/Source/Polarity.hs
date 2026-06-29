{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Coo.Source.Polarity where

import Coo.Source.Syntax
import Coo.Source.Print ()

import qualified Data.Map as M
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Monad.Except

import Prettyprinter

data Unified a = Unknown | Same a | Conflict
  deriving (Show, Eq, Ord, Functor)

instance Eq a => Semigroup (Unified a) where
  Same x <> Same y
    | x == y   = Same x
  x <> Unknown = x
  Unknown <> y = y
  _ <> _       = Conflict

instance Eq a => Monoid (Unified a) where
  mempty = Unknown

instance (Pretty a) => Pretty (Unified a) where
  pretty (Same a) = pretty a
  pretty Unknown  = pretty "<unknown>"
  pretty Conflict = pretty "<conflict>"

newtype PolInEnv  = PolIn { fromCxt :: M.Map Parameter Strat }
  deriving (Show, Eq, Semigroup, Monoid)

newtype PolOutEnv = PolOut { toCxt :: M.Map Parameter (Unified Strat) }
  deriving (Show, Eq)

instance Semigroup PolOutEnv where
  PolOut env <> PolOut env' = PolOut $ M.unionWith (<>) env env'

instance Monoid PolOutEnv where
  mempty  = PolOut M.empty
  mconcat = PolOut . M.unionsWith (<>) . fmap toCxt

instance Pretty PolOutEnv where
  pretty (PolOut env) = vsep
    [ pretty x <+> pretty ":" <+> pretty s
    | (x, s) <- M.toList env ]

data PolarityError = UnknownTermPolarity Term
                   | MispolarReaction (Maybe Strat) Reaction
                   | UnpolarizedCommand Statement
                   | UnboundConstraints PolOutEnv
  deriving (Show)

instance Pretty PolarityError where
  pretty (UnknownTermPolarity t) = vsep
    [ pretty "Could not determine polarity of:",
      indent 4 (pretty t) ]
  pretty (MispolarReaction Nothing r) = vsep
    [ pretty "Expected a guarded reaction, but instead found:",
      indent 4 (pretty (abridgeReaction r)) ]
  pretty (MispolarReaction (Just s) r) = vsep
    [ pretty "Expected a" <+> pretty s <+> pretty "reaction, but instead found:",
      indent 4 (pretty (abridgeReaction r)) ]
  pretty (UnpolarizedCommand c) = vsep
    [ pretty "Cannot infer a polarity for the command:",
      indent 4 (pretty c) ]
  pretty (UnboundConstraints env) = vsep
    [ pretty "Unbound variables used outside of defining context:",
      indent 4 (pretty env) ]

type MonadPolar m = (MonadReader PolInEnv m, MonadWriter PolOutEnv m, MonadError PolarityError m)

type PolarizeT m = ExceptT PolarityError (RWST PolInEnv PolOutEnv () m)

type Polarize = PolarizeT Identity

runPolarizeT :: Monad m => PolarizeT m a -> PolInEnv -> m (Either PolarityError a, PolOutEnv)
runPolarizeT m r = do (x, _, out) <- runRWST (runExceptT m) r ()
                      return (x, out)

runPolarize :: Polarize a -> PolInEnv -> (Either PolarityError a, PolOutEnv)
runPolarize m r = runIdentity $ runPolarizeT m r

semiclosedPolarity :: (MonadPolar m) => m a -> m a
semiclosedPolarity m = do
  (a, env) <- listen m
  if M.null (toCxt env)
    then return a
    else throwError $ UnboundConstraints env


quickTermPolarity :: (MonadReader PolInEnv m) => Term -> m (Maybe (Unified Strat))
quickTermPolarity Nil          = return $ Just $ Same CBV
quickTermPolarity (Pair _ _)   = return $ Just $ Same CBV
quickTermPolarity (Make _ _)   = return $ Just $ Same CBV
quickTermPolarity (Obj _)      = return $ Just $ Same CBV
quickTermPolarity (Call _)     = return $ Just $ Same CBV
quickTermPolarity (App _ _)    = return $ Just $ Same CBN
quickTermPolarity (Dot _ _)    = return $ Just $ Same CBN
quickTermPolarity (Fn _)       = return $ Just $ Same CBN
quickTermPolarity (Shift s _)  = return $ Just $ Same $ shiftTo s
quickTermPolarity (AsType t a) = case castAnnote a of
  Annote (Check s) _ -> return $ Just $ Same s
  _                  -> quickTermPolarity t
quickTermPolarity (Do r)       = quickReactionPolarity r
quickTermPolarity (Var x)      = do
  cxt <- fromCxt <$> ask
  return $ case M.lookup x cxt of
    Just s  -> Just $ Same s
    Nothing -> Nothing

quickReactionPolarity :: (MonadReader PolInEnv m) => Reaction -> m (Maybe (Unified Strat))
quickReactionPolarity (Any _ `Rest` _) = return $ Just $ Unknown
quickReactionPolarity (_     `Rest` _) = return $ Just $ Same CBN
quickReactionPolarity (_     `Pop`  _) = return $ Just $ Same CBN
quickReactionPolarity (_     `Proj` _) = return $ Just $ Same CBN
quickReactionPolarity (_     `Rec`  _) = return $ Just $ Same CBN
quickReactionPolarity (Exec _)         = return $ Just $ Unknown
quickReactionPolarity (Eval t)         = quickTermPolarity t
quickReactionPolarity (Guard _ _ r)    = quickReactionPolarity r
quickReactionPolarity (LetFun _ _ r)   = quickReactionPolarity r
quickReactionPolarity (Else _ r)       = quickReactionPolarity r
quickReactionPolarity Cede             = return $ Nothing
quickReactionPolarity (r1 `Alt` r2)    = (<>) <$> p1 <*> p2
  where p1 = quickReactionPolarity r1
        p2 = quickReactionPolarity r2

autoPolarizeTerm :: (MonadPolar m) => Term -> m (Maybe Term)
autoPolarizeTerm t = do
  quick_strat <- quickTermPolarity t
  case quick_strat of
    Just (Same s) -> Just <$> polarizeTerm s t
    _             -> return Nothing

autoPolarizeReaction :: (MonadPolar m) => Reaction -> m (Maybe Reaction)
autoPolarizeReaction r = do
  quick_strat <- quickReactionPolarity r
  case quick_strat of
    Just (Same s) -> Just <$> polarizeReact s r
    _             -> return Nothing


autoShift :: Strat -> Strat -> Term -> Term
autoShift CBV CBN = Shift (PS CBN You)
autoShift CBN CBV = Shift (PS CBV You)
autoShift _   _   = id

autoShiftTarget :: Strat -> Strat -> CoTerm -> CoTerm
autoShiftTarget CBV CBN = Shift (PS CBV Me)
autoShiftTarget CBN CBV = Shift (PS CBN Me)
autoShiftTarget _   _   = id

autoGoTo :: Term -> Strat -> Maybe Annotation -> Strat -> Maybe Term -> Statement
autoGoTo u s a s' Nothing  =
  Go (autoShift s s' u) (Just $ strategizeAnnote (Check s') a) Nothing
autoGoTo u s a s' (Just t) =
  Go u (Just $ strategizeAnnote (Check s) a) (Just $ autoShiftTarget s' s t)

directTypeAnnote :: (MonadPolar m)
                 => Term -> Maybe Annotation -> Maybe Term
                 -> m (Maybe Annotation)
directTypeAnnote u ann t = do
  left <- mustCheckTerm u
  right <- mustCheckGoToTarget t
  case (left, right) of
    (False, True)  -> return $ Just $ assignTypeAnnote GoTo ann
    (True, False)  -> return $ Just $ assignTypeAnnote ToGo ann
    (False, False) -> return $ Just $ assignTypeAnnote GoTo ann
    _              -> return ann

mustCheckTerm :: (MonadPolar m) => Term -> m Bool
mustCheckTerm (App _ _)    = return False
mustCheckTerm (Dot _ _)    = return False
mustCheckTerm (AsType _ _) = return False
mustCheckTerm (Var x)      = do
  env <- fromCxt <$> ask
  return $ not $ M.member x env
mustCheckTerm (Do r)       = return $ mustCheckReact r
mustCheckTerm (Fn r)       = return $ mustCheckReact r
mustCheckTerm (Obj t)      = mustCheckTerm t
mustCheckTerm (Call t)     = mustCheckTerm t
mustCheckTerm (Shift _ t)  = mustCheckTerm t
mustCheckTerm _            = return True

mustCheckGoToTarget :: (MonadPolar m) => Maybe Term -> m Bool
mustCheckGoToTarget t = case t of
  Nothing -> mustCheckTerm (Var (Implicit Context))
  Just u  -> mustCheckTerm u

mustCheckReact :: Reaction -> Bool
mustCheckReact (Eval _)         = False
mustCheckReact (Exec _)         = False
mustCheckReact (Rest (Any _) r) = mustCheckReact r
mustCheckReact _                = True

polarizeTerm :: (MonadPolar m) => Strat -> Term -> m Term
polarizeTerm CBV Nil        = return Nil
polarizeTerm CBV (Pair w v) = Pair <$> polarizeTerm CBV w <*> polarizeTerm CBV v
polarizeTerm CBV (Make i v) = Make i <$> polarizeTerm CBV v
polarizeTerm CBV (Obj u)    = Obj <$> polarizeTerm CBN u
polarizeTerm CBV (Call u)   = Call <$> polarizeTerm CBN u
polarizeTerm CBN (App u v)  = App <$> polarizeTerm CBN u <*> polarizeTerm CBV v
polarizeTerm CBN (Dot u i)  = Dot <$> polarizeTerm CBN u <*> pure i
polarizeTerm CBN (Fn r)     = Fn <$> polarizeReact CBN r
polarizeTerm CBN (Do r)     = Do <$> polarizeReact CBN r
polarizeTerm CBV (Do r)
  | isAction r              = Do <$> polarizeReact CBV r
  | otherwise               = autoShift CBN CBV . Do <$> polarizeReact CBN r
polarizeTerm s (Shift p t)
  | s == shiftTo p          = Shift p <$> polarizeTerm (shiftTo p) t
polarizeTerm s (AsType t a) = AsType <$> polarizeTerm s t <*> pure (strategizeCast (Check s) a)
polarizeTerm s t@(Var x)    = do
  cxt <- fromCxt <$> ask
  case M.lookup x cxt of
    Just p  -> return $ autoShift p s t
    Nothing -> do tell $ PolOut $ M.singleton x (Same s)
                  return t
polarizeTerm s t            = do
  p <- quickTermPolarity t
  case p of
    Just (Same s') -> autoShift s' s <$> polarizeTerm s' t
    _              -> throwError $ UnknownTermPolarity t

polarizeReact :: (MonadPolar m) => Strat -> Reaction -> m Reaction
polarizeReact s   (Eval t)         = Eval <$> polarizeTerm s t
polarizeReact s   (Exec c)         = bindPolarity (Implicit Context) (opStrat s)
                                   $ Exec <$> polarizeCmd c
polarizeReact CBV (Any x `Rest` r) = bindPolarity x CBN $ Rest (Any x) <$> polarizeGuard r
polarizeReact CBN (p `Rest` r)     = bindPatPolarity p $ Rest p <$> polarizeGuard r
polarizeReact CBN (p `Pop` r)      = bindPatPolarity p $ Pop p <$> polarizeReact CBN r
polarizeReact CBN (i `Proj` r)     = Proj i <$> polarizeReact CBN r
polarizeReact CBN (q `Rec` r)      = bindCopatPolarity q $ Rec q <$> polarizeReact CBN r
polarizeReact s   (Guard m t r)    = case m of
  Just p  -> Guard m <$> polarizeTerm CBV t <*> bindPatPolarity p (polarizeReact s r)
  Nothing -> Guard m <$> polarizeTerm CBV t <*> polarizeReact s r
polarizeReact s   (Else x r)       = bindPolarity x CBN $ Else x <$> polarizeReact s r
polarizeReact _ Cede               = return Cede
polarizeReact s (r1 `Alt` r2)      = Alt <$> polarizeReact s r1 <*> polarizeReact s r2
polarizeReact s r                  = throwError $ MispolarReaction (Just s) r

polarizeGuard :: (MonadPolar m) => Reaction -> m Reaction
polarizeGuard (Exec c)      = Exec <$> polarizeCmd c
polarizeGuard (Guard m t r) = case m of
  Just p  -> Guard m <$> polarizeTerm CBV t <*> bindPatPolarity p (polarizeGuard r)
  Nothing -> Guard m <$> polarizeTerm CBV t <*> polarizeGuard r
polarizeGuard (Else x r)    = bindPolarity x CBN $ Else x <$> polarizeGuard r
polarizeGuard Cede          = return Cede
polarizeGuard (r1 `Alt` r2) = Alt <$> polarizeGuard r1 <*> polarizeGuard r2
polarizeGuard r             = throwError $ MispolarReaction Nothing r

polarizeCaveat :: (MonadPolar m) => SetCaveat -> m SetCaveat
polarizeCaveat (p, t) = (p,) <$> polarizeTerm CBV t

polarizeStmt :: (MonadPolar m) => Statement -> m Statement
polarizeStmt (Run t)                = Run <$> polarizeTerm CBV t
polarizeStmt (LocalFun d r)         = case extractFunName d r of
  Just x  -> bindPolarity x CBN $ LocalFun d <$> polarizeReact CBN r
  Nothing -> LocalFun d <$> polarizeReact CBN r
polarizeStmt (Case t r)             = Case <$> polarizeTerm CBV t <*> polarizeReact CBN r
polarizeStmt (If r)                 = If <$> polarizeGuard r
polarizeStmt (SetMatch p t grd els) = do
  t' <- polarizeTerm CBV t
  grd' <- traverse polarizeCaveat grd
  els' <- traverse (polarizeReact CBN) els
  return $ SetMatch p t' grd' els'

polarizeStmt (Go u a t)
  | Just s <- a >>= fromDir . stratOf  = do
  u' <- polarizeTerm s u
  t' <- polarizeGoToTarget (opStrat s) t
  a' <- directTypeAnnote u' a t'
  return $ Go u' a' t'
polarizeStmt c@(Go u a t)           = do
  s_u <- quickTermPolarity u
  s_t <- case t of
    Just e  -> quickTermPolarity e
    Nothing -> quickTermPolarity (Var (Implicit Context))
  let s = s_u <> fmap (fmap opStrat) s_t
  case (s_u, s, s_t) of
    (_, Just (Same s'), _) -> do
      u' <- polarizeTerm s' u
      t' <- polarizeGoToTarget (opStrat s') t
      a' <- strategizeAnnote (Check s') <$> directTypeAnnote u' a t'
      return $ Go u' (Just a') t'
    (Just (Same s1), Just Conflict, Just (Same s2)) -> do
      u' <- polarizeTerm s1 u
      t' <- polarizeGoToTarget s2 t
      a' <- directTypeAnnote u' a t'
      return $ autoGoTo u' s1 a' (opStrat s2) t'
    _ -> throwError $ UnpolarizedCommand c

polarizeGoToTarget :: (MonadPolar m) => Strat -> Maybe Term -> m (Maybe Term)
polarizeGoToTarget s (Just t) = Just <$> polarizeTerm s t
polarizeGoToTarget s Nothing  = do polarizeTerm s (Var (Implicit Context))
                                   return Nothing

polarizeCmd :: (MonadPolar m) => Command -> m Command
polarizeCmd []    = return []
polarizeCmd (s:c) = (:) <$> polarizeStmt s <*> bindStmtPolarity s (polarizeCmd c)

bindPolarity :: (MonadReader PolInEnv m) => Parameter -> Strat -> m a -> m a
bindPolarity x s = local (PolIn (M.singleton x s) <>)

patPolarityEnv :: Pattern -> PolInEnv
patPolarityEnv (Any x)      = PolIn $ M.singleton x CBV
patPolarityEnv (IsObj x)    = PolIn $ M.singleton x CBN
patPolarityEnv IsNil        = PolIn $ M.empty
patPolarityEnv (IsPair p q) = patPolarityEnv q <> patPolarityEnv p
patPolarityEnv (Made _ p)   = patPolarityEnv p

copatPolarityEnv :: CoPattern -> PolInEnv
copatPolarityEnv (SelfIs x)    = PolIn $ M.singleton x CBN
copatPolarityEnv (q `CoApp` p) = patPolarityEnv p <> copatPolarityEnv q
copatPolarityEnv (q `CoDot` _) = copatPolarityEnv q

bindPatPolarity :: (MonadReader PolInEnv m) => Pattern -> m a -> m a
bindPatPolarity p = local (patPolarityEnv p <>)

bindCopatPolarity :: (MonadReader PolInEnv m) => CoPattern -> m a -> m a
bindCopatPolarity q = local (copatPolarityEnv q <>)

stmtPolarityEnv :: Statement -> PolInEnv
stmtPolarityEnv s = case s of
  LocalFun d r
    | Just x <- extractFunName d r  -> PolIn $ M.singleton x CBN
  SetMatch p _ (Just (Just q, _)) _ -> patPolarityEnv q <> patPolarityEnv p
  SetMatch p _ _                  _ -> patPolarityEnv p
  _                                 -> PolIn M.empty

cmdPolarityEnv :: Command -> PolInEnv
cmdPolarityEnv cmd = foldMap stmtPolarityEnv cmd

bindStmtPolarity :: MonadReader PolInEnv m => Statement -> m a -> m a
bindStmtPolarity s = local (stmtPolarityEnv s <>)
