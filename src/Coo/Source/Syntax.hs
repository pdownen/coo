{-# LANGUAGE DeriveFunctor #-}
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
  | LocalFun FunDeclare Reaction
  | SetMatch Pattern Term (Maybe SetCaveat) (Maybe Reaction)
  | If Reaction
  | Case Term Reaction
  deriving (Show)

type FunDeclare = (Maybe Variable, Maybe Type)
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
  | Term `AsType` TypeCast
  | Shift PolarityShift Term
  deriving (Show)

type CoTerm = Term

data TypeCast = PrefixType Annotation | PostfixType Annotation
  deriving (Show)

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
  | LetFun FunDeclare Reaction Reaction
  | Else Parameter Reaction
  | Reaction `Alt` Reaction
  | Cede
  deriving (Show)

data Declaration
  = Field Pattern Term
  | Function FunDeclare Reaction
  deriving (Show)

type Bindings = [Declaration]

data Module
  = Package Bindings Term
  deriving (Show)

data Annotation = Annote { stratOf :: Dir Strat, typeOf :: Dir Type }
  deriving (Show, Eq, Ord)

data Dir a = Check a | GoTo | ToGo | Infer
  deriving (Show, Eq, Ord, Functor)

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
  = VarTy Variable
  | RecTy Variable Type
  | UnitTy
  | Type `PairTy` Type
  | Type `ArrowTy` Type
  | Type `ArrDoTy` Type
  | TagTy [(Literal, Type)]
  | ObjTy Type
  deriving (Show, Eq, Ord)

instance Semigroup Reaction where
  (<>) = Alt
  
instance Monoid Reaction where
  mempty = Cede

pattern Blank :: Parameter
pattern Blank = Unbound "_"

pattern IntTyName, FloatTyName, StringTyName, BoolTyName :: Variable
pattern IntTyName    = "int"
pattern FloatTyName  = "float"
pattern StringTyName = "string"
pattern BoolTyName   = "bool"

pattern IntTy, FloatTy, StringTy, BoolTy :: Type
pattern IntTy    = VarTy IntTyName
pattern FloatTy  = VarTy FloatTyName
pattern StringTy = VarTy StringTyName
pattern BoolTy   = VarTy BoolTyName

pattern TrueName, FalseName :: TagName
pattern TrueName  = "True"
pattern FalseName = "False"

pattern TrueTag, FalseTag :: Literal
pattern TrueTag  = Tag TrueName
pattern FalseTag = Tag FalseName

pattern TruePat, FalsePat :: Pattern
pattern TruePat  = Made TrueTag  IsNil
pattern FalsePat = Made FalseTag IsNil

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

extractFunName :: FunDeclare -> Reaction -> Maybe Parameter
extractFunName (Just x, _)  _ = Just $ Bound x
extractFunName (Nothing, _) r = extractSelfName r

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

emptyFunDecl :: FunDeclare
emptyFunDecl = (Nothing, Nothing)

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

abridgeReaction :: Reaction -> Reaction
abridgeReaction Cede          = Cede
abridgeReaction (r1 `Alt` r2) = abridgeReaction r1 `Alt` abridgeReaction r2
abridgeReaction (q `Rec` r)   = q `Rec` abridgeReaction r
abridgeReaction (p `Rest` r)  = p `Rest` abridgeReaction r
abridgeReaction (p `Pop` r)   = p `Pop` abridgeReaction r
abridgeReaction (i `Proj` r)  = i `Proj` abridgeReaction r
abridgeReaction (Guard p t r) = Guard p t (abridgeReaction r)
abridgeReaction _             = Cede

endRunGoes :: Maybe Annotation -> Command -> Command
endRunGoes a = endRunGoesTo a Nothing

endRunGoesTo :: Maybe Annotation -> Maybe CoTerm -> Command -> Command
endRunGoesTo a k [Run u] = [Go u a k]
endRunGoesTo _ _ []      = []
endRunGoesTo a k (s:c)   = s : endRunGoesTo a k c

pattern OfPolarity :: Strat -> Annotation
pattern OfPolarity s = Annote (Check s) Infer

pattern OfType :: Type -> Annotation
pattern OfType t = Annote Infer (Check t)

pattern NoAnnote :: Annotation
pattern NoAnnote = Annote Infer Infer

pattern StratTy :: Strat -> Type -> Annotation
pattern StratTy s t = Annote (Check s) (Check t)

fromDir :: Dir a -> Maybe a
fromDir (Check a) = Just a
fromDir _         = Nothing

toDir :: Maybe a -> Dir a
toDir (Just a) = Check a
toDir Nothing  = Infer

strategizeAnnote :: Dir Strat -> Maybe Annotation -> Annotation
strategizeAnnote s Nothing  = Annote s Infer
strategizeAnnote s (Just a) = a{stratOf = s}

assignTypeAnnote :: Dir Type -> Maybe Annotation -> Annotation
assignTypeAnnote t         Nothing  = Annote Infer t
assignTypeAnnote (Check t) (Just a) = a{typeOf = Check t}
assignTypeAnnote t         (Just a) = case a of
  Annote _ (Check _) -> a
  Annote s _         -> Annote s t

strategizeCast :: Dir Strat -> TypeCast -> TypeCast
strategizeCast s (PrefixType a)  = PrefixType $ strategizeAnnote s (Just a)
strategizeCast s (PostfixType a) = PostfixType $ strategizeAnnote s (Just a)

castAnnote :: TypeCast -> Annotation
castAnnote (PrefixType a)  = a
castAnnote (PostfixType a) = a
