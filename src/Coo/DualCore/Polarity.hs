{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
module Coo.DualCore.Polarity where

import Coo.DualCore.Syntax
import Coo.DualCore.Print ()
import qualified Data.Map as M
import Control.Monad.Except

import Control.Monad.Identity
import Control.Monad.RWS

import Data.Bifoldable
import Data.Bitraversable

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

newtype PolInEnv x = PolIn { fromCxt :: M.Map x Strat }
  deriving (Show, Eq, Semigroup, Monoid)

newtype PolOutEnv x = PolOut { toCxt :: M.Map x (Unified Strat) }
  deriving (Show, Eq)

instance (Ord x) => Semigroup (PolOutEnv x) where
  PolOut env <> PolOut env' = PolOut $ M.unionWith (<>) env env'

instance (Ord x) => Monoid (PolOutEnv x) where
  mempty  = PolOut M.empty
  mconcat = PolOut . M.unionsWith (<>) . fmap toCxt

instance (Pretty x) => Pretty (PolOutEnv x) where
  pretty (PolOut env) = vsep
    [ pretty x <+> pretty ":" <+> pretty s
    | (x, s) <- M.toList env ]

instance (Pretty x) => Pretty (PolInEnv x) where
  pretty (PolIn env) = vsep
    [ pretty x <+> pretty ":" <+> pretty s
    | (x, s) <- M.toList env ]

data PolarityError x i
  = MispolarCommand Strat (Cmd x i (Dir Strat)) Strat
  | MispolarTerm Strat (Trm x i Strat) Strat
  | MispolarVariable Strat x Strat
  | UnpolarVariable x
  | MispolarAction x (Cmd x i Strat)
  | UnpolarAction x (Cmd x i Strat)
  | UnboundConstraints (PolOutEnv x)
  deriving (Show)

instance (Pretty x, Pretty i) => Pretty (PolarityError x i) where
  pretty (MispolarCommand s1 c s2) = vsep
    [ pretty "Mispolarized command:",
      indent 4 (pretty c),
      pretty "Go's polarity:" <+> pretty s1,
      pretty "To's polarity:" <+> pretty s2 ]
  pretty (MispolarTerm s1 t s2) = vsep
    [ pretty "Mispolarized term:",
      indent 4 (pretty t),
      pretty "Expected polarity:" <+> pretty s1,
      pretty "Inferred polarity:" <+> pretty s2 ]
  pretty (MispolarVariable s1 x s2) = vsep
    [ pretty "Mispolarized use of variable:" <+> pretty x <> pretty ".",
      pretty "Expected polarity:" <+> pretty s1,
      pretty "Inferred polarity:" <+> pretty s2 ]
  pretty (UnpolarVariable x) = vsep
    [ pretty "Insufficient context to infer the polarity of" <+> pretty x ]
  pretty (MispolarAction x c) = vsep
    [ pretty "Cannot infer polarity of action:",
      indent 4 (pretty $ Act x c),
      pretty "Mispolarized conflicted use of its parameter." ]
  pretty (UnpolarAction x c) = vsep
    [ pretty "Cannot infer polarity of action:",
      indent 4 (pretty $ Act x c),
      pretty "No information inferrable about its parameter." ]
  pretty (UnboundConstraints env) = vsep
    [ pretty "Unbound variables used outside of defining context:",
      indent 4 (pretty env) ]

type MonadPolar x i m = (MonadReader (PolInEnv x) m,
                         MonadWriter (PolOutEnv x) m,
                         MonadError (PolarityError x i) m)

type PolarizeT x i m = ExceptT (PolarityError x i) (RWST (PolInEnv x) (PolOutEnv x) () m)

type Polarize x i = PolarizeT x i Identity

runPolarizeT :: Monad m
             => PolarizeT x i m a -> PolInEnv x
             -> m (Either (PolarityError x i) a, PolOutEnv x)
runPolarizeT m r = do (x, _, out) <- runRWST (runExceptT m) r ()
                      return (x, out)

runPolarize :: Polarize x i a -> PolInEnv x
            -> (Either (PolarityError x i) a, PolOutEnv x)
runPolarize m r = runIdentity $ runPolarizeT m r

semiclosedPolarity :: (MonadPolar x i m) => m a -> m a
semiclosedPolarity m = do
  (a, env) <- listen m
  if M.null (toCxt env)
    then return a
    else throwError $ UnboundConstraints env

quickTrmPolarity :: (MonadReader (PolInEnv x) m, Ord x)
                  => Trm x i o -> m (Maybe Strat)
quickTrmPolarity (New _)   = return $ Just CBV
quickTrmPolarity (Dat _)   = return $ Just CBV
quickTrmPolarity (Cod _)   = return $ Just CBN
quickTrmPolarity (Act _ _) = return Nothing
quickTrmPolarity (Var x)   = M.lookup x <$> (fromCxt <$> ask)

polarizeCmd :: (MonadPolar x i m, Ord x)
            => Cmd x i (Dir Strat) -> m (Cmd x i Strat)
polarizeCmd c@(Cut u o t) = case o of
  Check s -> Cut <$> checkTrmPolarity s u <*> pure s <*> checkCoTrmPolarity s t
  GoTo    -> do (u', s) <- inferTrmPolarity u
                t' <- checkCoTrmPolarity s t
                return $ Cut u' s t'
  ToGo    -> do (t', s) <- inferCoTrmPolarity t
                u' <- checkTrmPolarity s u
                return $ Cut u' s t'
  Infer   -> do (u', s1) <- inferTrmPolarity u
                (t', s2) <- inferCoTrmPolarity t
                if s1 == s2
                  then return $ Cut u' s1 t'
                  else throwError $ MispolarCommand s1 c s2

polarizeTrm :: (MonadPolar x i m, Ord x)
            => Maybe Strat -> Trm x i (Dir Strat) -> m (Trm x i Strat, Strat)
polarizeTrm Nothing  (New p)   = do
  p' <- bitraverse (checkTrmPolarity CBN) (checkTrmPolarity CBV) p
  return (New p', CBV)
polarizeTrm Nothing  (Dat v)   = do
  v' <- checkValPolarity v
  return (Dat v', CBV)
polarizeTrm Nothing  (Cod rs)  = do
  rs' <- traverse checkRspPolarity rs
  return (Cod rs', CBN)
polarizeTrm o        (Var x)   = do
  s <- polarizeVar o x
  return (Var x, s)
polarizeTrm (Just s) (Act x c) = do
  c' <- bindPolarity x (opp s) $ polarizeCmd c
  return (Act x c', s)
polarizeTrm Nothing  (Act x c) = pass $ do
  (c', env) <- listen $ polarizeCmd c
  case M.lookup x (toCxt env) of
    Just (Same s) -> do let unbind = PolOut . M.delete x . toCxt
                        return ((Act x c', opp s), unbind)
    Just Conflict -> throwError $ MispolarAction x c'
    _             -> throwError $ UnpolarAction x c'
polarizeTrm (Just s) t         = do
  r@(t', s') <- inferTrmPolarity t
  if s == s'
    then return r
    else throwError $ MispolarTerm s t' s'

inferTrmPolarity :: (MonadPolar x i m, Ord x)
                 => Trm x i (Dir Strat) -> m (Trm x i Strat, Strat)
inferTrmPolarity = polarizeTrm Nothing

checkTrmPolarity :: (MonadPolar x i m, Ord x)
                 => Strat -> Trm x i (Dir Strat) -> m (Trm x i Strat)
checkTrmPolarity s t = fst <$> polarizeTrm (Just s) t

polarizeCoTrm :: (MonadPolar x i m, Ord x)
            => Maybe Strat -> CoTrm x i (Dir Strat) -> m (CoTrm x i Strat, Strat)
polarizeCoTrm Nothing  t = do
  (t', s') <- polarizeTrm Nothing t
  return (t', opp s')
polarizeCoTrm (Just s) t = do
  (t', s') <- polarizeTrm (Just $ opp s) t
  return (t', opp s')

inferCoTrmPolarity :: (MonadPolar x i m, Ord x)
                   => CoTrm x i (Dir Strat) -> m (CoTrm x i Strat, Strat)
inferCoTrmPolarity = polarizeCoTrm Nothing

checkCoTrmPolarity :: (MonadPolar x i m, Ord x)
                   => Strat -> CoTrm x i (Dir Strat) -> m (CoTrm x i Strat)
checkCoTrmPolarity s t = fst <$> polarizeCoTrm (Just s) t


polarizeVar :: (MonadPolar x i m, Ord x)
            => Maybe Strat -> x -> m Strat
polarizeVar o x = do
  cxt <- fromCxt <$> ask
  case (o, M.lookup x cxt) of
    (Just s1, Just s2)
      | s1 == s2       -> return s2
      | otherwise      -> throwError $ MispolarVariable s1 x s2
    (Nothing, Just s)  -> return s
    (Just s,  Nothing) -> do tell $ PolOut $ M.singleton x (Same s)
                             return s
    (Nothing, Nothing) -> throwError $ UnpolarVariable x

checkVarPolarity :: (MonadPolar x i m, Ord x)
                 => Strat -> x -> m x
checkVarPolarity s x = do polarizeVar (Just s) x
                          return x

inferVarPolarity :: (MonadPolar x i m, Ord x)
                 => x -> m Strat
inferVarPolarity = polarizeVar Nothing

checkRspPolarity :: (MonadPolar x i m, Ord x)
                 => Rsp x i (Dir Strat) -> m (Rsp x i Strat)
checkRspPolarity (q :=> c) = do
  c' <- bindCopatPolarity q $ polarizeCmd c
  return $ q :=> c'

checkValPolarity :: (MonadPolar x i m, Ord x)
                 => Val x i (Dir Strat) x x -> m (Val x i Strat x x)
checkValPolarity (Struc p) = do
  p' <- bitraverse checkClsPolarity (checkVarPolarity CBV) p
  return $ Struc p'

checkClsPolarity :: (MonadPolar x i m, Ord x)
                 => Cls x i (Dir Strat) x x -> m (Cls x i Strat x x)
checkClsPolarity (Free x)  = Free <$> checkVarPolarity CBN x
checkClsPolarity (u :/: e) = (:/:) <$> checkTrmPolarity CBN u <*> polarizeEnv e

polarizeEnv :: (MonadPolar x i m, Ord x)
            => Env x i (Dir Strat) x x -> m (Env x i Strat x x)
polarizeEnv = traverse polarizeBound

polarizeBound :: (MonadPolar x i m, Ord x)
              => Bound x i (Dir Strat) x x -> m (Bound x i Strat x x)
polarizeBound (LetVal o v) = case o of
  Check s -> LetVal s <$> checkValPolarity v
  _       -> LetVal CBV <$> checkValPolarity v
polarizeBound (LetFun o l) = case o of
  Check s -> LetFun s <$> checkClsPolarity l
  _       -> LetFun CBN <$> checkClsPolarity l


bindPolarity :: (MonadReader (PolInEnv x) m, Ord x) => x -> Strat -> m a -> m a
bindPolarity x s = local (PolIn (M.singleton x s) <>)

bindPatPolarity :: (MonadReader (PolInEnv x) m, Ord x) => Pat i x x -> m a -> m a
bindPatPolarity p = local (patPolarityEnv p <>)

bindCopatPolarity :: (MonadReader (PolInEnv x) m, Ord x) => CoPat i x x -> m a -> m a
bindCopatPolarity q = local (copatPolarityEnv q <>)

patPolarityEnv :: Ord x => Pat i x x -> PolInEnv x
patPolarityEnv = bifoldMap (PolIn . flip M.singleton CBN) (PolIn . flip M.singleton CBV)

copatPolarityEnv :: Ord x => CoPat i x x -> PolInEnv x
copatPolarityEnv (Just x  :.: p) = PolIn $ M.insert x CBN $ fromCxt $ patPolarityEnv p
copatPolarityEnv (Nothing :.: p) = patPolarityEnv p
