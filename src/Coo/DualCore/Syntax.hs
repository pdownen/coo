{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Coo.DualCore.Syntax where

import qualified Data.Map as M
import Control.Monad (ap)
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable

data Cmd x i o
  = Cut { go :: Trm x i o,
          as :: o,
          to :: Trm x i o }
  deriving (Show, Functor)

data Trm x i o
  = Var x
  | Act x (Cmd x i o)
  | Cod [Rsp x i o]
  | Dat (Val x i o x x)
  {-
  | Dat (Struc (Pat i (Cls x i o x x) x))
  -}
  | New (Pat i (Trm x i o) (Trm x i o))
  {-
  | New (A (Trm x i o))
  | New (C (Trm x i o))
  | New MT
  | New (Trm x i o :*: Trm x i o)
  | New (i :@: Trm x i o)
  -}
  deriving (Show)

type CoTrm = Trm

data Rsp x i o
  = CoPat i x x :=> Cmd x i o
  deriving (Show, Functor)

data CoPat i c a
  = (Maybe c) :.: Pat i c a
  deriving (Show, Functor, Foldable, Traversable)

getSelf :: CoPat i c a -> Maybe c
getSelf (c :.: _) = c

getPat :: CoPat i c a -> Pat i c a
getPat (_ :.: p) = p

data Pat i c a
  = A !a
  | C !c
  | MT
  | !(Pat i c a) :*: !(Pat i c a)
  | !i :@: !(Pat i c a)
  deriving (Show, Eq, Functor, Foldable, Traversable)

newtype Val x i o c a = Struc { splat :: Pat i (Cls x i o c a) a }
  deriving (Show, Eq)
{-
data Val x i o a
  = Struc (A a)
  | Struc (C (Cls x i o a))
  | Struc MT
  | Struc (Val x i o a :*: Val x i o a)
  | Struc (i :@: Val x i o a)
  deriving (Show, Functor, Foldable, Traversable)
-}

data Cls x i o c a
  = Trm x i o :/: Env x i o c a
  | Free c
  deriving (Show, Functor, Foldable, Traversable)

type Env x i o c a = M.Map x (Bound x i o c a)

data Bound x i o c a
  = LetVal o (Val x i o c a)
  | LetFun o (Cls x i o c a)
  deriving (Show, Functor, Foldable, Traversable)

data Dir o = GoTo | ToGo | Infer | Check o
  deriving (Show, Eq, Functor)

data Type x i
  = VarTy x
--  | RecTy x (Type x i)
  | UnitTy
  | Type x i `PairTy` Type x i
  | TagTy (M.Map i (Type x i))
  | ObjTy (Type x i)
  | SameTypeAs x
  deriving (Show, Ord)

data Strat = CBV | CBN
  deriving (Show, Eq, Bounded, Enum)

opp :: Strat -> Strat
opp CBV = CBN
opp CBN = CBV

instance (Eq c) => Eq (Cls x i o c a) where
  Free x == Free y = x == y
  _ == _ = False

instance (Ord x, Ord i) => Eq (Type x i) where
  s == t = openTypeEquality (freeTypeVars s) s t

instance Bifunctor (Pat i) where
  bimap _ g (A x) = A (g x)
  bimap f _ (C x) = C (f x)
  bimap _ _ MT    = MT
  bimap f g (p :*: q) = bimap f g p :*: bimap f g q
  bimap f g (i :@: q) = i :@: bimap f g q

instance Bifoldable (Pat i) where
  bifoldMap _ g (A x)     = g x
  bifoldMap f _ (C x)     = f x
  bifoldMap _ _ MT        = mempty
  bifoldMap f g (p :*: q) = bifoldMap f g p <> bifoldMap f g q
  bifoldMap f g (_ :@: q) = bifoldMap f g q

instance Bitraversable (Pat i) where
  bitraverse _ g (A x)     = A <$> g x
  bitraverse f _ (C x)     = C <$> f x
  bitraverse _ _ MT        = pure MT
  bitraverse f g (p :*: q) = (:*:) <$> bitraverse f g p <*> bitraverse f g q
  bitraverse f g (i :@: q) = (i :@:) <$> bitraverse f g q

instance Applicative (Pat i c) where
  pure  = A
  (<*>) = ap

instance Monad (Pat i c) where
  A x     >>= f = f x
  C x     >>= _ = C x
  MT      >>= _ = MT
  p :*: q >>= f = (p >>= f) :*: (q >>= f)
  i :@: q >>= f = i :@: (q >>= f)

instance Bifunctor (CoPat i) where
  bimap f g (x :.: p) = (f <$> x) :.: bimap f g p

instance Bifoldable (CoPat i) where
  bifoldMap f g (x :.: p) = (foldMap f x) <> bifoldMap f g p

instance Bitraversable (CoPat i) where
  bitraverse f g (x :.: p) = (:.:) <$> (traverse f x) <*> bitraverse f g p

instance Functor (Val x i o c) where
  fmap f (Struc p) = Struc $ bimap (fmap f) f p

instance Bifunctor (Val x i o) where
  bimap f g (Struc p) = Struc $ bimap (bimap f g) g p

instance Foldable (Val x i o c) where
  foldMap f (Struc p) = bifoldMap (foldMap f) f p

instance Traversable (Val x i o c) where
  traverse f (Struc p) = Struc <$> bitraverse (traverse f) f p

instance Applicative (Val x i o c) where
  pure  = Struc . pure
  (<*>) = ap

instance Monad (Val x i o c) where
  Struc (A x)     >>= f = f x
  Struc MT        >>= _ = Struc MT
  Struc (p :*: q) >>= f = Struc $ splat (Struc p >>= f) :*: splat (Struc q >>= f)
  Struc (i :@: q) >>= f = Struc $ i :@: splat (Struc q >>= f)
  Struc (C l)     >>= f = Struc $ C (locally l)
    where locally (u :/: e)  = u :/: (subst <$> e)
          locally (Free c)   = Free c
          subst (LetVal o v) = LetVal o (v >>= f)
          subst (LetFun o d) = LetFun o (locally d)

instance Bifunctor (Cls x i o) where
  bimap f g (u :/: e) = u :/: fmap (bimap f g) e
  bimap f _ (Free c)  = Free (f c)

instance Bifunctor (Bound x i o) where
  bimap f g (LetVal o v) = LetVal o (bimap f g v)
  bimap f g (LetFun o l) = LetFun o (bimap f g l)

instance Functor (Trm x i) where
  fmap _ (Var x)   = Var x
  fmap f (Act x c) = Act x (fmap f c)
  fmap f (Cod rs)  = Cod [fmap f r | r <- rs]
  fmap f (Dat v)   = Dat (mapPoleVal f v)
  fmap f (New p)   = New (bimap f' f' p)
    where f' = fmap f

castPat :: Pat i c a -> Maybe (Pat i c' a')
castPat MT        = Just MT
castPat (i :@: p) = (i :@:) <$> castPat p
castPat (p :*: q) = (:*:) <$> castPat p <*> castPat q
castPat _         = Nothing

data GenericPat i where
  GenPat :: Pat i c a -> GenericPat i

data Elide = Elide
  deriving (Show, Eq, Ord, Enum, Bounded)

instance (Show i) => Show (GenericPat i) where
  show (GenPat p) = show $ bimap (const Elide) (const Elide) p

mapPoleVal :: (o -> p) -> Val x i o c a -> Val x i p c a
mapPoleVal f (Struc p) = Struc $ first (mapPoleCls f) p

mapPoleCls :: (o -> p) -> Cls x i o c a -> Cls x i p c a
mapPoleCls _ (Free c)  = Free c
mapPoleCls f (t :/: e) = fmap f t :/: fmap (mapPoleBound f) e

mapPoleBound :: (o -> p) -> Bound x i o c a -> Bound x i p c a
mapPoleBound f (LetVal o v) = LetVal (f o) (mapPoleVal f v)
mapPoleBound f (LetFun o c) = LetFun (f o) (mapPoleCls f c)

getPoleBound :: Bound x i o c a -> o
getPoleBound (LetVal o _) = o
getPoleBound (LetFun o _) = o

mapVarCmd :: Ord y => (x -> y) -> Cmd x i o -> Cmd y i o
mapVarCmd f (Cut t o u) = Cut (mapVarTrm f t) o (mapVarTrm f u)

mapVarTrm :: Ord y => (x -> y) -> Trm x i o -> Trm y i o
mapVarTrm f (Var x)   = Var (f x)
mapVarTrm f (Act x c) = Act (f x) (mapVarCmd f c)
mapVarTrm f (Cod rs)  = Cod [ mapVarRsp f r | r <- rs ]
mapVarTrm f (New p)   = New (bimap (mapVarTrm f) (mapVarTrm f) p)
mapVarTrm f (Dat v)   = Dat (mapVarDatVal f v)

mapVarRsp :: Ord y => (x -> y) -> Rsp x i o -> Rsp y i o
mapVarRsp f (q :=> c) = bimap f f q :=> mapVarCmd f c

mapVarDatVal :: Ord y => (x -> y) -> Val x i o x x -> Val y i o y y
mapVarDatVal f (Struc p) = Struc (bimap (mapVarClsVal f) f p)

mapVarClsVal :: Ord y => (x -> y) -> Cls x i o x x -> Cls y i o y y
mapVarClsVal f (Free x)  = Free (f x)
mapVarClsVal f (t :/: e) = mapVarTrm f t :/: e'
  where e' = M.mapKeys f $ fmap (mapVarBoundVal f) e

mapVarBoundVal :: Ord y => (x -> y) -> Bound x i o x x -> Bound y i o y y
mapVarBoundVal f (LetVal o v) = LetVal o (mapVarDatVal f v)
mapVarBoundVal f (LetFun o c) = LetFun o (mapVarClsVal f c)

freeTypeVars :: (Ord x) => Type x i -> M.Map x x
freeTypeVars (VarTy x)      = M.singleton x x
-- freeTypeVars (RecTy x t)    = M.delete x $ freeTypeVars t
freeTypeVars UnitTy         = M.empty
freeTypeVars (s `PairTy` t) = freeTypeVars s <> freeTypeVars t
freeTypeVars (TagTy xts)    = M.unions [ freeTypeVars t | (_, t) <- M.toList xts ]
freeTypeVars (ObjTy t)      = freeTypeVars t
freeTypeVars (SameTypeAs _) = M.empty

renameTypeVars :: (Ord x) => M.Map x x -> Type x i -> Type x i
renameTypeVars sub (VarTy x)      = case M.lookup x sub of
  Just y  -> VarTy y
  Nothing -> VarTy x
-- renameTypeVars sub (RecTy x t)
--   | M.null sub'                  = RecTy x t
--   | otherwise                    = RecTy x $ renameTypeVars sub' t
--   where sub' = M.delete x sub
renameTypeVars _   UnitTy         = UnitTy
renameTypeVars sub (s `PairTy` t) = renameTypeVars sub s `PairTy` renameTypeVars sub t
renameTypeVars sub (TagTy zts)    = TagTy $ renameTypeVars sub <$> zts
renameTypeVars sub (ObjTy t)      = ObjTy $ renameTypeVars sub t
renameTypeVars _   (SameTypeAs x) = SameTypeAs x

openTypeEquality :: (Ord x, Ord i) => M.Map x x -> Type x i -> Type x i -> Bool
openTypeEquality eq s t = case (s, t) of
  (VarTy x, VarTy y) -> case M.lookup x eq of
    Nothing -> False
    Just z  -> y == z
--  (RecTy x s', RecTy y t') -> openTypeEquality (M.insert x y eq) s' t'
  (ObjTy s', ObjTy t') -> openTypeEquality eq s' t'
  (UnitTy, UnitTy) -> True
  (s1 `PairTy` s2, t1 `PairTy` t2) ->
    openTypeEquality eq s1 t1 && openTypeEquality eq s2 t2
  (TagTy xss, TagTy yts) -> M.keys xss == M.keys yts
    && and [ sameTagEq x s' | (x, s') <- M.toList xss ]
    where sameTagEq x s'
            | Just t' <- M.lookup x yts = openTypeEquality eq s' t'
            | otherwise                 = False
  (SameTypeAs x, SameTypeAs y) -> x == y
  (_, _) -> False

