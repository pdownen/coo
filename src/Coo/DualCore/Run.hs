{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Coo.DualCore.Run where

import Coo.DualCore.Syntax
import Coo.DualCore.Focus
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State

data Extern x i o c a f = Extern
  { callExternal :: o -> c -> Val x i o c a -> f (Cmd x i o),
    unhandledPat :: o -> [Pat i x x] -> Val x i o c a -> f (Cmd x i o),
    expectedData :: o -> Trm x i o -> Trm x i o -> f (Cmd x i o),
    expectedCode :: o -> Trm x i o -> Val x i o c a -> f (Cmd x i o),
    undefinedData :: x -> f (Val x i o c a),
    undefinedCode :: x -> f (Cls x i o c a),
    illdefinedData :: x -> o -> Cls x i o c a -> f (Val x i o c a),
    illdefinedCode :: x -> o -> Val x i o c a -> f (Cls x i o c a)
   }

data Global x i o c a f = Global
  { extern   :: Extern x i o c a f,
    focusing :: FocusSettings o x Int,
    locals   :: Env x i o c a }

-- Main runtime loop

type MonadRun x i o c a f m
  = (MonadState (Global x i o c a f) m)

loop :: (Ord x, Eq i, MonadRun x i Strat c a m m)
     => Cmd x i Strat -> m r
loop c = do c' <- step c
            loop c'

loopBy :: (Ord x, Eq i, MonadRun x i Strat c a m m)
       => (m (Cmd x i Strat) -> m (Cmd x i Strat))
       -> Cmd x i Strat -> m r
loopBy h c = do c' <- h $ step c
                loopBy h c'

-- Single step of execution

step :: (Eq i, Ord x, MonadRun x i Strat c a m m)
     => Cmd x i Strat -> m (Cmd x i Strat)
step (Cut t CBV u) = act CBV t u
step (Cut u CBN t) = act CBN t u

act :: (Eq i, Ord x, MonadRun x i Strat c a m m)
    => Strat -> Trm x i Strat -> Trm x i Strat
    -> m (Cmd x i Strat)
act o (Act x c) u = do
  bindFun x o u
  return c
act o (New p) u = do
  FocAs note z f k <- focusing <$> get
  let (p', _, bs) = case o of
                      CBV -> gatherSubTrmsFromBy z f note p
                      CBN -> gatherSubTrmsFromBy z f (flipNote note) p
  bindFun k o u
  case o of
    CBV -> return $ sequenceDatActs bs $ sendNewDat o p' (Var k)
    CBN -> return $ sequenceCoDatActs bs $ sendNewCoDat o p' (Var k)
act o (Var x) u = do
  v <- fetchVal x
  react o u v
act o (Dat v) u = do
  w <- buildVal v
  react o u w
act o t u = do
  ex <- extern <$> get
  expectedData ex o t u

react :: (Eq i, Ord x, MonadRun x i Strat c a m m)
      => Strat -> Trm x i Strat -> Val x i Strat c a
      -> m (Cmd x i Strat)
react o (Var x) v = do
  l <- fetchCls x
  sendToCls o v l
  {-
  f <- enterCls l
  case f of
    Right u -> react o u v
    Left  c -> do ex <- extern <$> get
                  callExternal ex o c v
  -}
react o (Act x c) v = do
  bindVal x o v
  return c
react o u@(Cod rs) v = case switch o rs (splat v) of
    Just (c, x, bs) -> do l <- close u
                          let env = case x of
                                Nothing -> bs
                                Just self -> M.insert self (LetFun o l) bs
                          binds env
                          return c
    Nothing         -> do ex <- extern <$> get
                          let ps = [p | _ :.: p :=> _ <- rs]
                          unhandledPat ex o ps v
react o u v = do
  ex <- extern <$> get
  expectedCode ex o u v

-- (Co)pattern matching

match :: (Eq i, Ord x)
      => o -> Pat i x x -> Pat i (Cls x i o c a) a
      -> Maybe (Env x i o c a)
match o (A x)     v         = return $ M.singleton x (LetVal o (Struc v))
match o (C x)     (C l)     = return $ M.singleton x (LetFun o l)
match _ MT        MT        = return M.empty
match o (p :*: q) (w :*: v) = M.union <$> match o p w <*> match o q v
match o (i :@: q) (j :@: v)
  | i == j                  = match o q v
match _ _         _         = Nothing

switch :: (Ord x, Eq i)
       => o -> [Rsp x i o] -> Pat i (Cls x i o c a) a
       -> Maybe (Cmd x i o, Maybe x, Env x i o c a)
switch _ []                   _ = Nothing
switch o (x :.: p :=> c : rs) v = case match o p v of
  Just bs -> return (c, x, bs)
  Nothing -> switch o rs v

-- Building / focusing on new structures at run-time

buildStruc :: (Ord x, MonadRun  x i o c a m m)
           => Pat i (Cls x i o x x) x
           -> m (Pat i (Cls x i o c a) a)
buildStruc (A x)     = splat <$> fetchVal x
buildStruc (C l)     = C <$> buildCls l
buildStruc MT        = return MT
buildStruc (p :*: q) = (:*:) <$> buildStruc p <*> buildStruc q
buildStruc (i :@: q) = (i :@:) <$> buildStruc q

buildVal :: (Ord x, MonadRun  x i o c a m m)
         => Val x i o x x -> m (Val x i o c a)
buildVal (Struc p) = Struc <$> buildStruc p

buildCls :: (MonadRun x i o c a m m, Ord x)
         => Cls x i o x x -> m (Cls x i o c a)
buildCls (Free x)  = fetchCls x
buildCls (u :/: e) = (u :/:) <$> traverse inlineBound e

inlineBound :: (MonadRun x i o c a m m, Ord x)
            => Bound x i o x x -> m (Bound x i o c a)
inlineBound (LetVal o v) = LetVal o <$> buildVal v
inlineBound (LetFun o l) = LetFun o <$> buildCls l

{-
focus :: (Ord x, MonadRun x i o c a f m)
      => o -> Pat i (Trm x i o) (Trm x i' o')
      -> m (Pat i (Cls x i o x x) x, [(x, Trm x i' o')])
focus o p = runWriterT (focusAside o p)

focusAside :: (Ord x, MonadRun x i o c a f m, MonadWriter [(x, Trm x i' o')] m)
           => o -> Pat i (Trm x i o) (Trm x i' o')
           -> m (Pat i (Cls x i o x x) x)
focusAside o p = do
  env <- locals <$> get
  nameSubTrms o env p

nameSubTrms :: (Ord x, MonadRun x i o c a f m, MonadWriter [(x, Trm x i' o')] m)
            => o -> Env x i o c a -> Pat i (Trm x i o) (Trm x i' o')
            -> m (Pat i (Cls x i o x x) x)
nameSubTrms _ _ (A t)     = A <$> nameAct t
nameSubTrms o e (C u)     = C . Free <$> nameCls o e u
nameSubTrms _ _ MT        = return MT
nameSubTrms o e (p :*: q) = (:*:) <$> nameSubTrms o e p <*> nameSubTrms o e q
nameSubTrms o e (i :@: q) = (i :@:) <$> nameSubTrms o e q

nameAct :: (MonadAlloc x m, MonadWriter [(x, Trm x i' o')] m)
        => Trm x i' o' -> m x
nameAct (Var x) = return x
nameAct t       = do
  x <- fresh
  tell [(x, t)]
  return x

nameCls :: (Ord x, MonadRun x i o c a f m)
        => o -> Env x i o c a -> Trm x i o -> m x
nameCls _ _ (Var x) = return x
nameCls o e u       = do
  x <- fresh
  bindCls x o (u :/: e)
  return x

sequenceActs :: Strat -> [(x, Trm x i Strat)] -> Cmd x i Strat -> Cmd x i Strat
sequenceActs _ []           c = c
sequenceActs CBV ((x,t):bs) c = Cut t CBV (Act x $ sequenceActs CBV bs c)
sequenceActs CBN ((k,t):bs) c = Cut (Act k $ sequenceActs CBN bs c) CBN t

newStruc :: Strat -> Val x i Strat x x -> Trm x i Strat -> Cmd x i Strat
newStruc CBV p u = Cut (Dat p) CBV u
newStruc CBN q u = Cut u CBN (Dat q)
-}

-- Substituting the global environment into values, patterns, and local environments

fetchVal :: (MonadRun x i o c a m m, Ord x) => x -> m (Val x i o c a)
fetchVal x = do
  e <- get
  case M.lookup x (locals e) of
    Just (LetVal _ v) -> return v
    Just (LetFun o l) -> illdefinedData (extern e) x o l
    Nothing           -> undefinedData (extern e) x

fetchCls :: (MonadRun x i o c a m m, Ord x) => x -> m (Cls x i o c a)
fetchCls x = do
  e <- get
  case M.lookup x (locals e) of
    Just (LetFun _ l) -> return l
    Just (LetVal o v) -> illdefinedCode (extern e) x o v
    Nothing           -> undefinedCode (extern e) x

close :: MonadState (Global x i o c a f) m => Trm x i o -> m (Cls x i o c a)
close u = (u :/:) <$> (locals <$> get)

enterCls :: MonadState (Global x i o c a f) m
         => Cls x i o c a -> m (Either c (Trm x i o))
enterCls (u :/: e) = do
  modify (\st -> st{locals = e})
  return $ Right u
enterCls (Free c) = return $ Left c

sendToCls :: (Ord x, MonadState (Global x i Strat c a m) m, Eq i)
          => Strat -> Val x i Strat c a -> Cls x i Strat c a
          -> m (Cmd x i Strat)
sendToCls o v l = do
  f <- enterCls l
  case f of
    Right u -> react o u v
    Left  c -> do ex <- extern <$> get
                  callExternal ex o c v

free :: (MonadState (Global x i o c a f) m, Ord x) => S.Set x -> m ()
free unused
  | null unused = return ()
  | otherwise   = do env <- get
                     let env' = M.fromSet (const mt) unused
                     put env{locals = locals env M.\\ env'}
    where mt = LetVal CBV (Struc MT)

binds :: (MonadState (Global x i o c a f) m, Ord x) => Env x i o c a -> m ()
binds bs = do
  env <- get
  let env' = bs `M.union` locals env
  put env{locals = env'}

bindVal :: (MonadState (Global x i o c a f) m, Ord x) => x -> o -> Val x i o c a -> m ()
bindVal x o v = binds $ M.singleton x $ LetVal o v

bindCls :: (MonadState (Global x i o c a f) m, Ord x) => x -> o -> Cls x i o c a -> m ()
bindCls x o l = binds $ M.singleton x $ LetFun o l

bindFun :: (MonadState (Global x i o c a f) m, Ord x) => x -> o -> Trm x i o -> m ()
bindFun x o u = do
  env <- locals <$> get
  bindCls x o (u :/: env)
