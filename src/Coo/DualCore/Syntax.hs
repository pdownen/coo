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

data Type x i = TyVar x
  deriving (Show, Functor)

data Dir o = GoTo | ToGo | Infer | Check o
  deriving (Show, Eq, Functor)

data Strat = CBV | CBN
  deriving (Show, Eq, Bounded, Enum)

opp :: Strat -> Strat
opp CBV = CBN
opp CBN = CBV

instance (Eq c) => Eq (Cls x i o c a) where
  Free x == Free y = x == y
  _ == _ = False

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

mapPoleVal :: (o -> p) -> Val x i o c a -> Val x i p c a
mapPoleVal f (Struc p) = Struc $ first (mapPoleCls f) p

mapPoleCls :: (o -> p) -> Cls x i o c a -> Cls x i p c a
mapPoleCls _ (Free c)  = Free c
mapPoleCls f (t :/: e) = fmap f t :/: fmap (mapPoleBound f) e

mapPoleBound :: (o -> p) -> Bound x i o c a -> Bound x i p c a
mapPoleBound f (LetVal o v) = LetVal (f o) (mapPoleVal f v)
mapPoleBound f (LetFun o c) = LetFun (f o) (mapPoleCls f c)

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
