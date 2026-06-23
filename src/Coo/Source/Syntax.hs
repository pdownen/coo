{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
module Coo.Source.Syntax where

import Data.Text
import Control.Applicative

type Variable = Text
type TagName = Text
data Parameter = Bound Variable | Unbound Variable | Implicit Label
  deriving (Show, Eq, Ord)

data Label
  = Here
  | Join
  | Self
  | Other
  | Context
  | Unmatched
  deriving (Show, Eq, Ord, Enum, Bounded)

data Literal
  = Int !Integer
  | Flt !Double
  | Str !Text
  | Tag !TagName
  deriving (Show, Eq, Ord)

data Statement
  = Go Term (Maybe Annotation) (Maybe Term)
  | Run Term
  | LocalFun Reaction
  | SetMatch Pattern Term (Maybe SetCaveat) (Maybe Reaction)
  | If Reaction
  | Case Term Reaction
  deriving (Show)

type SetCaveat = (Maybe Pattern, Term)

type Command = [Statement]

data Term
  = Var Parameter
  | Do Reaction
  | Fn Reaction
  | Nil
  | Term `Pair` Term
  | Term `App` Term
  | Obj Term
  | Call Term
  | Make Literal Term
  | Term `Dot` Literal
  -- | Term `Get` Variable
  | Shift PolarityShift Term
  deriving (Show)

type CoTerm = Term

data Pattern
  = Any Parameter
--  | Many (Maybe Pattern) Parameter
  | Made Literal Pattern
  | Pattern `IsPair` Pattern
  | IsNil
  | IsObj Parameter
  deriving (Show)

data CoPattern
  = SelfIs Parameter
  | CoPattern `CoApp` Pattern
  | CoPattern `CoDot` Literal
  deriving (Show)

data Reaction
  = Eval Term
  | Exec Command
  | Pattern `Rest` Reaction
  | Pattern `Pop` Reaction
  | Literal `Proj` Reaction
  | CoPattern `Rec` Reaction
  | Guard (Maybe Pattern) Term Reaction
  | LetFun Reaction Reaction
  | Else Parameter Reaction
  | Reaction `Alt` Reaction
  | Cede
  deriving (Show)

data Declaration
  = Field Pattern Term
  | Function Reaction
  deriving (Show)

type Bindings = [Declaration]

data Module
  = Package Bindings Term
  deriving (Show)

data Annotation
  = OfType Type
  | OfPolarity Strat
  deriving (Show)

data PolarityShift = PS { shiftTo :: Strat, whoShifts :: Who }
  deriving (Show, Eq)

data Strat = CBV | CBN
  deriving (Show, Eq, Ord, Enum, Bounded)

data Who = Me | You
  deriving (Show, Eq, Ord, Enum, Bounded)

opStrat :: Strat -> Strat
opStrat CBV = CBN
opStrat CBN = CBV

data Type
  = TyVar Variable
  deriving (Show)

instance Semigroup Reaction where
  (<>) = Alt
  
instance Monoid Reaction where
  mempty = Cede

isAction :: Reaction -> Bool
isAction (Eval _)         = True
isAction (Exec _)         = True
isAction (Guard _ _ r)    = isAction r
isAction Cede             = True
isAction (r1 `Alt` r2)    = isAction r1 && isAction r2
isAction (Any _ `Rest` r) = isAction r
isAction _                = False

isConditional :: Reaction -> Bool
isConditional (Eval _)      = True
isConditional (Exec _)      = True
isConditional (Guard _ _ r) = isConditional r
isConditional Cede          = True
isConditional (r1 `Alt` r2) = isConditional r1 && isConditional r2
isConditional _             = False

extractSelfName :: Reaction -> Maybe Parameter
extractSelfName (q `Rec` _)   = extractSelfBind q
extractSelfName (r `Alt` r')  = extractSelfName r <|> extractSelfName r'
extractSelfName (Guard _ _ r) = extractSelfName r
extractSelfName _             = Nothing

extractSelfBind :: CoPattern -> Maybe Parameter
extractSelfBind (SelfIs (Unbound _)) = Nothing
extractSelfBind (SelfIs x)           = Just x
extractSelfBind (q `CoApp` _)        = extractSelfBind q
extractSelfBind (q `CoDot` _)        = extractSelfBind q

copatToTerm :: CoPattern -> Term
copatToTerm (SelfIs x)    = Var x
copatToTerm (q `CoApp` p) = copatToTerm q `App` patToTerm p
copatToTerm (q `CoDot` i) = copatToTerm q `Dot` i

patToTerm :: Pattern -> Term
patToTerm (Any x)      = Var x
patToTerm (IsObj x)    = Obj (Var x)
patToTerm IsNil        = Nil
patToTerm (IsPair p q) = Pair (patToTerm p) (patToTerm q)
patToTerm (Made i p)   = Make i (patToTerm p)

reassocToPat :: CoPattern -> Pattern -> (Maybe Parameter, Pattern)
reassocToPat (SelfIs (Unbound _)) p = (Nothing, p)
reassocToPat (SelfIs x)           p = (Just x, p)
reassocToPat (q `CoApp` p')       p = reassocToPat q (p' `IsPair` p)
reassocToPat (q `CoDot` i)        p = reassocToPat q (i `Made` p)

reassocToCoPat :: CoPattern -> Pattern -> (CoPattern, Pattern)
reassocToCoPat q (p' `IsPair` p) = reassocToCoPat (q `CoApp` p') p
reassocToCoPat q (i `Made` p)    = reassocToCoPat (q `CoDot` i) p
reassocToCoPat q p               = (q, p)


pattern TruePat, FalsePat :: Pattern
pattern TruePat = Made (Tag "True") IsNil
pattern FalsePat = Made (Tag "False") IsNil

pattern Blank :: Parameter
pattern Blank = Unbound "_"

abridgeReaction :: Reaction -> Reaction
abridgeReaction Cede          = Cede
abridgeReaction (r1 `Alt` r2) = abridgeReaction r1 `Alt` abridgeReaction r2
abridgeReaction (q `Rec` r)   = q `Rec` abridgeReaction r
abridgeReaction (p `Rest` r)  = p `Rest` abridgeReaction r
abridgeReaction (p `Pop` r)   = p `Pop` abridgeReaction r
abridgeReaction (i `Proj` r)  = i `Proj` abridgeReaction r
abridgeReaction (Guard p t r) = Guard p t (abridgeReaction r)
abridgeReaction _             = Cede

endRunGoesTo :: CoTerm -> Command -> Command
endRunGoesTo k [Run u] = [Go u (Just (OfPolarity CBV)) (Just k)]
endRunGoesTo _ []      = []
endRunGoesTo k (s:c)   = s : endRunGoesTo k c
