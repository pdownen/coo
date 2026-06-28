{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
module Coo.DualCore.Sugar where

import Coo.DualCore.Syntax
import Coo.Source.Syntax (Literal(..))
import Coo.Data.Namespace
import qualified Data.Text as Txt
import Prettyprinter

data Label = Blank
           | Here
           | It
           | Join
           | Self
           | Other
           | Context
           | Unmatched
           | Temp Int
           deriving (Show, Eq, Ord)

instance Pretty Label where
  pretty Blank     = pretty "_"
  pretty Here      = pretty "here"
  pretty It        = pretty "it"
  pretty Join      = pretty "join"
  pretty Self      = pretty "self"
  pretty Other     = pretty "other"
  pretty Context   = pretty "context"
  pretty Unmatched = pretty "unmatched"
  pretty (Temp n)  = pretty "temp" <> pretty n

pattern HereVar, ItVar, CtxtVar, JoinVar, SelfVar, OtherVar
  :: Trm (Reserve Label x) i o

pattern HereVar  = Var (Internal Here)
pattern ItVar    = Var (Internal It)
pattern CtxtVar  = Var (Internal Context)
pattern JoinVar  = Var (Internal Join)
pattern SelfVar  = Var (Internal Self)
pattern OtherVar = Var (Internal Other)

pattern BlankPat :: Pat i c (Reserve Label a)
pattern BlankPat = A (Internal Blank)

pattern NonRecCoPat :: Pat i c a -> CoPat i c a
pattern NonRecCoPat p = Nothing :.: p

pattern BlankCoPat :: CoPat i c (Reserve Label a)
pattern BlankCoPat = NonRecCoPat BlankPat

pattern HerePat :: Pat i c (Reserve Label a)
pattern HerePat = A (Internal Here)

pattern SelfCoPat :: Pat i (Reserve Label c) a
                  -> CoPat i (Reserve Label c) a
pattern SelfCoPat p = Just (Internal Self) :.: p

pattern HereCoPat :: CoPat i (Reserve Label c) (Reserve Label a)
pattern HereCoPat = SelfCoPat HerePat

pattern TruePat, FalsePat :: Pat Literal c a

pattern TruePat <- (isTrue -> True)
  where TruePat = Tag (Txt.pack "True") :@: MT

pattern FalsePat <- (isFalse -> True)
  where FalsePat = Tag (Txt.pack "False") :@: MT

isTrue, isFalse :: Pat Literal c a -> Bool

isTrue (Tag t :@: MT)
  | t == Txt.pack "True" = True
isTrue _                 = False

isFalse (Tag t :@: MT)
  | t == Txt.pack "False" = True
isFalse _                 = False


----------------
-- Statements --
----------------


pattern Go     t a = Cut t a CtxtVar
pattern GoHere t a = Cut t a HereVar
pattern GoJoin t a = Cut t a JoinVar

pattern GoToCont t = Cut NilVal (Check CBV, Check UnitTy) t

pattern GoToJoin = GoJoin NilVal (Check CBV, Check UnitTy)

pattern SetMatchElse p t rs c
  = Cut t (Check CBV, GoTo) (Cod ((NonRecCoPat p :=> c) : rs))

pattern SetMatch p t c
  = SetMatchElse p t [Cede] c

pattern FallOut = GoHere OtherVar (Check CBN, ToGo)

pattern FallThrough = Cut NilVal (Check CBV, Check UnitTy) OtherVar

pattern LocalValAs x a v c = Cut v (Check CBV, a) (Act x c)
pattern LocalActAs x a t c = Cut t (Check CBN, a) (Act x c)
pattern LocalCoActAs x a t c = Cut (Act x c) (Check CBV, a) t

pattern LocalVal x v c = LocalValAs x GoTo v c -- Cut v (Check CBV, GoTo) (Act x c)
pattern LocalAct x t c = LocalActAs x GoTo t c -- Cut t (Check CBN, GoTo) (Act x c)
pattern LocalCoAct x t c = LocalCoActAs x ToGo t c -- Cut (Act x c) (Check CBV, ToGo) t

pattern LocalFunAs x a t c = LocalActAs x a t c
pattern LocalFun x t c = LocalActAs x ToGo t c
pattern LocalFunAlts x rs c = LocalFun x (Cod rs) c

pattern LocalAltAs  a t c = LocalCoActAs (Internal Other) a t c
pattern LabelJoinAs a k c = LocalCoActAs (Internal Join) a k c
pattern ReContextAs a k c = LocalValAs (Internal Context) a k c

pattern LocalAlt  t c = LocalAltAs (Check (SameTypeAs (Internal Other))) t c
pattern LabelJoin k c = LabelJoinAs (Check UnitTy) k c
pattern ReContext k c = ReContextAs GoTo k c

pattern LocalSelf x k c
  = LocalAct x (DoHere (Cut SelfVar (Check CBN, GoTo) k)) c

pattern LocalOther k c
  = LocalAct (Internal Other) (DoHere (Cut k (Check CBV, ToGo) OtherVar)) c

pattern LocalElse k c
  = LocalActAs (Internal Other) (Check UnitTy)
               (Abort (Cut k (Check CBV, ToGo) OtherVar))
    c

pattern NoOther   c = LocalAltAs (Check (SameTypeAs (Internal Self))) (Cod []) c
pattern SkipOther c = LocalAltAs (Check UnitTy) (Abort GoToJoin) c

pattern AndThen c1 c2 = LabelJoinAs (Check UnitTy) (Abort c2) c1

pattern Case t rs = Cut t (Check CBV, GoTo) (Cod rs)


---------------
-- Reactions --
---------------

pattern DefaultCoPat = NonRecCoPat HerePat

pattern Cede = DefaultCoPat :=> FallOut

pattern ElseHere = BlankCoPat :=> FallOut

pattern Else = BlankCoPat :=> FallThrough

pattern Otherwise main other = DefaultCoPat :=> LocalAlt (DoHere other) main

pattern Try r = Cod [r, Cede]

pattern TryHere r = Cut HereVar (Check CBV, GoTo) (Try r)

pattern GuardHere r = Cod [r, ElseHere]

pattern Guard r = Cod [r, Else]

-----------
-- Terms --
-----------

pattern Lit :: i -> Trm x i o
pattern Lit i = New (i :@: MT)

pattern LitVal :: i -> Trm x i o
pattern LitVal i = Dat (Struc (i :@: MT))

pattern Do c = Act (Internal Context) c

pattern DoHere c = Act (Internal Here) c

pattern DoJoin c = Act (Internal Join) c

pattern Abort c = Act (Internal Blank) c

pattern Nil = New MT

pattern NilVal :: Trm x i o
pattern NilVal = Dat (Struc MT)

pattern Pair :: Trm x i o -> Trm x i o -> Trm x i o
pattern Pair t u = New (A t :*: A u)

pattern PairX :: x -> x -> Trm x i o
pattern PairX x y = Dat (Struc (A x :*: A y))

pattern Make :: i -> Trm x i o -> Trm x i o
pattern Make i t = New (i :@: A t)

pattern MakeX :: i -> x -> Trm x i o
pattern MakeX i x = Dat (Struc (i :@: A x))

pattern Push :: a -> Pat i c a -> Pat i c a
pattern Push u k = A u :*: k

pattern AppTo t u k = Cut t (Check CBN, GoTo) (New (Push u k))

pattern AppXTo t x k = Cut t (Check CBN, GoTo) (Dat (Struc (A x :*: k)))

pattern App t u = DoHere (AppTo t u (A HereVar))

pattern AppX t x = DoHere (AppXTo t x (A (Internal Here)))

pattern DotTo t i k = Cut t (Check CBN, GoTo) (New (i :@: k))

pattern DotTo' t i k = Cut t (Check CBN, GoTo) (Dat (Struc (i :@: k)))

pattern Dot t i = DoHere (DotTo t i (A HereVar))

pattern Dot' t i = DoHere (DotTo' t i (A (Internal Here)))

pattern Obj :: Trm x i o -> Trm x i o
pattern Obj t = New (C t)

pattern Thunk :: Trm x i o -> Trm x i o
pattern Thunk t = Obj t

pattern ForceCxt k = Cod [NonRecCoPat (C (Internal It))
                          :=>
                          Cut ItVar (Check CBN, GoTo) k]

pattern ForceTo t k = Cut t (Check CBV, GoTo) (ForceCxt k)

pattern Force t = DoHere (ForceTo t HereVar)
  {-
  (Cut
    t
    CheckCBV
    (Cod [NonRecCoPat (C (Internal It))
          :=>
          GoHere ItVar CheckCBN]))
  -}

pattern CallTo t k = Cut t (Check CBN, GoTo) (Thunk k)

pattern Call t = DoHere (CallTo t HereVar)
                 -- (Cut t CheckCBN (Obj HereVar))

pattern Return t = Cod [NonRecCoPat (C (Internal Here))
                        :=>
                        (Cut t (Check CBV, ToGo) HereVar)]

pattern CompleteObject rs a = DoHere (NoOther (GoHere (Cod rs) a))

pattern SelfInCxt k = DoHere (Cut SelfVar (Check CBN, GoTo) k)

pattern AsType t a = DoHere (GoHere t a)
