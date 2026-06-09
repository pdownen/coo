{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Coo.Data.Namespace where

import Control.Monad
import Control.Applicative
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable

import Prettyprinter

-- Identifiers with scoping metadata

data Scoped s a = a :#: s
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

infixl 2 :#:

instance (Pretty s, Pretty a) => Pretty (Scoped s a) where
  pretty (x :#: s) = pretty x <> pretty "_" <> pretty s

instance (Monoid s) => Applicative (Scoped s) where
  pure x = x :#: mempty
  (f :#: i) <*> (x :#: j) = f x :#: i <> j

instance (Monoid s) => Monad (Scoped s) where
  (x :#: i) >>= f = let (y :#: j) = f x
                    in y :#: i <> j

instance Bifunctor Scoped where
  bimap f g (x :#: i) = g x :#: f i

instance Bifoldable Scoped where
  bifoldMap f g (x :#: i) = g x <> f i

instance Bitraversable Scoped where
  bitraverse f g (x :#: i) = (:#:) <$> g x <*> f i

instance (Semigroup s, Semigroup a) => Semigroup (Scoped s a) where
  (x :#: i) <> (y :#: j) = x <> y :#: i <> j
  
instance (Monoid s, Monoid a) => Monoid (Scoped s a) where
  mempty = mempty :#: mempty

instance (Monoid a, Enum s) => Enum (Scoped s a) where
  succ = first succ
  pred = first pred
  toEnum n = mempty :#: toEnum n
  fromEnum (_ :#: i) = fromEnum i

  enumFrom       (x :#: n)                     = [ x :#: i | i <- enumFrom       n     ]
  enumFromThen   (x :#: n) (_ :#: k)           = [ x :#: i | i <- enumFromThen   n k   ]
  enumFromTo     (x :#: n)           (_ :#: m) = [ x :#: i | i <- enumFromTo     n   m ]
  enumFromThenTo (x :#: n) (_ :#: k) (_ :#: m) = [ x :#: i | i <- enumFromThenTo n k m ]

-- Reserving part of the namespace for internally generated variables

data Reserve b a
  = External a
  | Internal b
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Pretty b, Pretty a) => Pretty (Reserve b a) where
  pretty (External x) = pretty x
  pretty (Internal y) = backslash <> pretty y

instance Bifunctor Reserve where
  bimap f _ (Internal x) = Internal (f x)
  bimap _ g (External y) = External (g y)

instance Bifoldable Reserve where
  bifoldMap f _ (Internal x) = f x
  bifoldMap _ g (External y) = g y

instance Bitraversable Reserve where
  bitraverse f _ (Internal x) = Internal <$> f x
  bitraverse _ g (External y) = External <$> g y

instance Applicative (Reserve b) where
  pure  = External
  (<*>) = ap

instance Monad (Reserve b) where
  External x >>= f = f x
  Internal y >>= _ = Internal y

instance (Monoid b) => Alternative (Reserve b) where
  empty = Internal mempty
  
  External x <|> _ = External x
  _          <|> y = y

instance (Semigroup b, Semigroup a) => Semigroup (Reserve b a) where
  External x <> External y = External (x <> y)
  External x <> Internal _ = External x
  Internal _ <> External y = External y
  Internal x <> Internal y = Internal (x <> y)

instance (Monoid b, Semigroup a) => Monoid (Reserve b a) where
  mempty = empty

instance (Enum b, Enum a) => Enum (Reserve b a) where
  succ (Internal x) = Internal $ succ x
  succ (External x) = External $ succ x

  pred (Internal x) = Internal $ pred x
  pred (External x) = External $ pred x

  fromEnum (Internal x) = fromEnum x
  fromEnum (External x) = fromEnum x

  toEnum x = Internal $ toEnum x

  enumFrom (Internal x) = Internal <$> enumFrom x
  enumFrom (External x) = External <$> enumFrom x

  enumFromThen (Internal x) y = Internal <$> enumFromThen x (getInternalEnum y)
  enumFromThen (External x) y = External <$> enumFromThen x (getExternalEnum y)

  enumFromTo (Internal x) y = Internal <$> enumFromTo x (getInternalEnum y)
  enumFromTo (External x) y = External <$> enumFromTo x (getExternalEnum y)

  enumFromThenTo (Internal x) y z = Internal <$> enumFromThenTo x y' z'
    where y' = getInternalEnum y
          z' = getInternalEnum z
  enumFromThenTo (External x) y z = External <$> enumFromThenTo x y' z'
    where y' = getExternalEnum y
          z' = getExternalEnum z

getInternalEnum :: (Enum a, Enum b) => Reserve b a -> b
getInternalEnum (Internal b) = b
getInternalEnum (External a) = toEnum $ fromEnum a

getExternalEnum :: (Enum a, Enum b) => Reserve b a -> a
getExternalEnum (External a) = a
getExternalEnum (Internal b) = toEnum $ fromEnum b


-- An instance of arithmetic on internal reserved namespace, where external
-- names are all considered 0

reservedNum :: Num b => Reserve b a -> b
reservedNum (Internal n) = n
reservedNum (External _) = 0

instance (Num b) => Num (Reserve b a) where
  fromInteger = Internal . fromInteger

  x + y = Internal $ reservedNum x + reservedNum y
  x - y = Internal $ reservedNum x - reservedNum y
  x * y = Internal $ reservedNum x * reservedNum y
  abs x = Internal $ abs (reservedNum x)
  signum x = Internal $ signum (reservedNum x)


newtype Count a = Count {getCount :: a}
  deriving (Show, Eq, Ord, Bounded)

instance (Num a) => Num (Count a) where
  fromInteger = Count . fromInteger

  Count x + Count y = Count (x + y)
  Count x - Count y = Count (x - y)
  Count x * Count y = Count (x * y)
  abs (Count x)     = Count (abs x)
  signum (Count x)  = Count (signum x)

instance (Num a, Ord a) => Enum (Count a) where
  succ = (+ 1)
  pred = (subtract 1)

  toEnum n = Count (fromInteger (toInteger n))
  fromEnum = error "Data.Namespace.Enum.Count.fromEnum: undefined"

  enumFrom       start          = iterate succ start
  enumFromThen   start step     = iterate (+ step) start
  enumFromTo     start      end = takeWhile (<= end) $ iterate succ start
  enumFromThenTo start step end = takeWhile (<= end) $ iterate (+ step) start
