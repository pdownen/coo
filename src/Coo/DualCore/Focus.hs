{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Coo.DualCore.Focus where

import Coo.DualCore.Syntax
import Control.Monad.Reader
import Control.Monad.RWS
import Data.Bitraversable

-- Local focusing

type UnfocusedPat x i o = Pat i (Trm x i o) (Trm x i o)
type FocusedPat x i o = Pat i (Cls x i o x x) x

type SubFoci x i o = [(x, o, Trm x i o)]
data FociNote o = FociNote { asValue :: o, asCode :: o }

type MonadName x i o a m = (Enum a, MonadState a m,
                            MonadWriter (SubFoci x i o) m,
                            MonadReader (FociNote o) m)

stratFoci :: Strat -> FociNote Strat
stratFoci s = FociNote{asValue = s, asCode = opp s}

flipNote :: FociNote o -> FociNote o
flipNote (FociNote v c) = FociNote c v

nextId :: (Enum a, MonadState a m) => m a
nextId = do a <- get
            put (succ a)
            return a

locally :: (MonadState s m) => m a -> m a
locally m = do s <- get
               x <- m
               put s
               return x

gatherSubTrmsFromBy :: (Enum a)
                    => a -> (a -> x) -> FociNote o -> UnfocusedPat x i o
                    -> (FocusedPat x i o, a, SubFoci x i o)
gatherSubTrmsFromBy z f o p = runRWS (nameSubTrmsBy f p) o z

gatherSubTrmsBy :: (Enum a, Monoid a)
                => (a -> x) -> FociNote o -> UnfocusedPat x i o
                -> (FocusedPat x i o, a, SubFoci x i o)
gatherSubTrmsBy = gatherSubTrmsFromBy mempty

gatherSubTrmsFrom :: (Enum x)
                  => x -> FociNote o -> UnfocusedPat x i o
                  -> (FocusedPat x i o, x, SubFoci x i o)
gatherSubTrmsFrom z o p = runRWS (nameSubTrms p) o z

gatherSubTrms :: (Enum x, Monoid x)
              => FociNote o -> UnfocusedPat x i o
              -> (FocusedPat x i o, x, SubFoci x i o)
gatherSubTrms = gatherSubTrmsFrom mempty

nameSubTrmsBy :: (MonadName x i o a m)
              => (a -> x) -> UnfocusedPat x i o -> m (FocusedPat x i o)
nameSubTrmsBy f p = do
  ann <- ask
  let p' = fuseNewPats p
  bitraverse (fmap Free . nameTrmBy f (asCode ann)) (nameTrmBy f (asValue ann)) p'

nameSubTrms :: (MonadName x i o x m)
            => UnfocusedPat x i o -> m (FocusedPat x i o)
nameSubTrms p = do
  ann <- ask
  let p' = fuseNewPats p
  bitraverse (fmap Free . nameTrm (asCode ann)) (nameTrm (asValue ann)) p'

nameTrm :: (MonadName x i o x m)
        => o -> Trm x i o -> m x
nameTrm = nameTrmBy id

nameTrmBy :: (MonadName x i o a m)
          => (a -> x) -> o -> Trm x i o -> m x
nameTrmBy _ _ (Var x) = return x
nameTrmBy f o t       = do
  a <- nextId
  let x = f a
  tell [(x, o, t)]
  return x

fuseNewPats :: UnfocusedPat x i o -> UnfocusedPat x i o
fuseNewPats p = do
  v <- p
  case v of
    New p' -> fuseNewPats p'
    _      -> return v

sequenceDatActs :: SubFoci x i o -> Cmd x i o -> Cmd x i o
sequenceDatActs []           c = c
sequenceDatActs ((x,o,t):bs) c = Cut t o (Act x $ sequenceDatActs bs c)

sequenceCoDatActs :: SubFoci x i o -> Cmd x i o -> Cmd x i o
sequenceCoDatActs []           c = c
sequenceCoDatActs ((x,o,t):bs) c = Cut (Act x $ sequenceDatActs bs c) o t

sendNewDat :: o -> FocusedPat x i o -> Trm x i o -> Cmd x i o
sendNewDat o p u = Cut (Dat (Struc p)) o u

sendNewCoDat :: o -> FocusedPat x i o -> CoTrm x i o -> Cmd x i o
sendNewCoDat o p u = Cut u o (Dat (Struc p))

-- Global focusing

data FocusSettings o x l = FocAs { fociNote :: FociNote o,
                                   tempZero :: l,
                                   nameTemp :: l -> x,
                                   nameHere :: x }

type MonadFocus o x l m = (Enum l, MonadReader (FocusSettings o x l) m)
type FocusT o x l = ReaderT (FocusSettings o x l)
type Focus o x l = Reader (FocusSettings o x l)

runFocusT :: FocusT o x l m a -> FocusSettings o x l -> m a
runFocusT = runReaderT

runFocus :: Focus o x l a -> FocusSettings o x l -> a
runFocus = runReader

focusCmd :: (MonadFocus o x l m) => Cmd x i o -> m (Cmd x i o)
focusCmd (Cut u o e) = Cut <$> focusTrm o u <*> pure o <*> focusCoTrm o e

focusTrm :: (MonadFocus o x l m) => o -> Trm x i o -> m (Trm x i o)
focusTrm _ (Var x)   = return $ Var x
focusTrm _ (Act x c) = Act x <$> focusCmd c
focusTrm _ (Cod rs)  = Cod <$> traverse focusRsp rs
focusTrm _ (Dat v)   = return $ Dat v
focusTrm o (New p)   = do
  FocAs note z f k <- ask
  let (p', _, bs) = gatherSubTrmsFromBy z f note p
  case bs of
    [] -> return $ Dat (Struc p')
    _  -> do bs' <- traverse (\(x, o', t) -> (x, o',) <$> focusTrm o' t) bs
             return $ Act k $ sequenceDatActs bs' $ sendNewDat o p' (Var k)

focusCoTrm :: (MonadFocus o x l m) => o -> CoTrm x i o -> m (CoTrm x i o)
focusCoTrm _ (Var x)   = return $ Var x
focusCoTrm _ (Act x c) = Act x <$> focusCmd c
focusCoTrm _ (Cod rs)  = Cod <$> traverse focusRsp rs
focusCoTrm _ (Dat v)   = return $ Dat v
focusCoTrm o (New p)   = do
  FocAs note z f k <- ask
  let (p', _, bs) = gatherSubTrmsFromBy z f note p
  case bs of
    [] -> return $ Dat (Struc p')
    _  -> do bs' <- traverse (\(x, o', t) -> (x, o',) <$> focusTrm o' t) bs
             return $ Act k $ sequenceDatActs bs' $ sendNewCoDat o p' (Var k)

focusRsp :: (MonadFocus o x l m) => Rsp x i o -> m (Rsp x i o)
focusRsp (q :=> c) = (q :=>) <$> focusCmd c
