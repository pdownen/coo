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


pattern Go, GoHere, GoJoin :: Trm (Reserve Label x) i o -> o -> Cmd (Reserve Label x) i o

pattern Go     t a = Cut t a CtxtVar
pattern GoHere t a = Cut t a HereVar
pattern GoJoin t a = Cut t a JoinVar

pattern GoToCont :: CoTrm x i (Dir (Reserve Strat o))
                 -> Cmd x i (Dir (Reserve Strat o))
pattern GoToCont t = Cut NilVal CheckCBV t

pattern GoToJoin :: Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern GoToJoin = GoJoin NilVal CheckCBV

pattern SetMatchElse :: Pat i c c
                     -> Trm c i (Dir (Reserve Strat a))
                     -> [Rsp c i (Dir (Reserve Strat a))]
                     -> Cmd c i (Dir (Reserve Strat a))
                     -> Cmd c i (Dir (Reserve Strat a))
pattern SetMatchElse p t rs c
  = Cut t CheckCBV (Cod ((NonRecCoPat p :=> c) : rs))

pattern SetMatch :: Pat i (Reserve Label x) (Reserve Label x)
                 -> Trm (Reserve Label x) i (Dir (Reserve Strat a))
                 -> Cmd (Reserve Label x) i (Dir (Reserve Strat a))
                 -> Cmd (Reserve Label x) i (Dir (Reserve Strat a))
pattern SetMatch p t c
  = SetMatchElse p t [Cede] c

pattern FallOut :: Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern FallOut = GoHere OtherVar CheckCBN

pattern FallThrough :: Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern FallThrough = Cut NilVal CheckCBV OtherVar

pattern LocalVal, LocalFun, LocalAct, LocalCoAct
  :: x
  -> Trm x i (Dir (Reserve Strat o))
  -> Cmd x i (Dir (Reserve Strat o))
  -> Cmd x i (Dir (Reserve Strat o))
pattern LocalVal x v c = Cut v CheckCBV (Act x c)
pattern LocalAct x t c = Cut t CheckCBN (Act x c)
pattern LocalCoAct x t c = Cut (Act x c) CheckCBV t
pattern LocalFun x t c = LocalAct x t c

pattern LocalFunAlts :: x
                     -> [Rsp x i (Dir (Reserve Strat a))]
                     -> Cmd x i (Dir (Reserve Strat a))
                     -> Cmd x i (Dir (Reserve Strat a))
pattern LocalFunAlts x rs c = LocalFun x (Cod rs) c

pattern LocalAlt, LabelJoin, ReContext
  :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
  -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
  -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern LocalAlt  t c = LocalCoAct (Internal Other) t c
pattern LabelJoin k c = LocalCoAct (Internal Join) k c
pattern ReContext k c = LocalVal (Internal Context) k c

pattern LocalSelf :: (Reserve Label x)
                  -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
                  -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
                  -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern LocalSelf x k c
  = LocalAct x (DoHere (Cut SelfVar CheckCBN k)) c

pattern LocalOther :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
                   -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
                   -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern LocalOther k c
  = LocalAct (Internal Other) (DoHere (Cut k CheckCBV OtherVar)) c

pattern NoOther, SkipOther
  :: Cmd (Reserve Label x) i (Dir (Reserve Strat o))
  -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern NoOther   c = LocalAlt (Cod []) c
pattern SkipOther c = LocalAlt (Abort GoToJoin) c

pattern AndThen :: Cmd (Reserve Label x) i (Dir (Reserve Strat o))
                -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
                -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern AndThen c1 c2 = LabelJoin (Abort c2) c1

pattern Case :: Trm x i (Dir (Reserve Strat o))
             -> [Rsp x i (Dir (Reserve Strat o))]
             -> Cmd x i (Dir (Reserve Strat o))
pattern Case t rs = Cut t CheckCBV (Cod rs)


---------------
-- Reactions --
---------------

pattern DefaultCoPat :: CoPat i c (Reserve Label o)
pattern DefaultCoPat = NonRecCoPat HerePat

pattern Cede :: Rsp (Reserve Label x) i (Dir (Reserve Strat o))
pattern Cede = DefaultCoPat :=> FallOut

pattern ElseHere :: Rsp (Reserve Label x) i (Dir (Reserve Strat o))
pattern ElseHere = BlankCoPat :=> FallOut

pattern Else :: Rsp (Reserve Label x) i (Dir (Reserve Strat o))
pattern Else = BlankCoPat :=> FallThrough

pattern Otherwise :: Cmd (Reserve Label a) i (Dir (Reserve Strat o))
                  -> Cmd (Reserve Label a) i (Dir (Reserve Strat o))
                  -> Rsp (Reserve Label a) i (Dir (Reserve Strat o))
pattern Otherwise main other = DefaultCoPat :=> LocalAlt (DoHere other) main

pattern Try :: Rsp (Reserve Label x) i (Dir (Reserve Strat o))
            -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern Try r = Cod [r, Cede]

pattern TryHere :: Rsp (Reserve Label x) i (Dir (Reserve Strat o))
                -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern TryHere r = Cut HereVar CheckCBV (Try r)

pattern GuardHere :: Rsp (Reserve Label x) i (Dir (Reserve Strat o))
                  -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern GuardHere r = Cod [r, ElseHere]

pattern Guard :: Rsp (Reserve Label x) i (Dir (Reserve Strat o))
              -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern Guard r = Cod [r, Else]

-----------
-- Terms --
-----------

pattern Lit :: i -> Trm x i o
pattern Lit i = New (i :@: MT)

pattern LitVal :: i -> Trm x i o
pattern LitVal i = Dat (Struc (i :@: MT))

pattern Do :: Cmd (Reserve Label a) i o -> Trm (Reserve Label a) i o
pattern Do c = Act (Internal Context) c

pattern DoHere :: Cmd (Reserve Label a) i o -> Trm (Reserve Label a) i o
pattern DoHere c = Act (Internal Here) c

pattern DoJoin :: Cmd (Reserve Label a) i o -> Trm (Reserve Label a) i o
pattern DoJoin c = Act (Internal Join) c

pattern Abort c = Act (Internal Blank) c

pattern Nil :: Trm x i o
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

pattern AppTo t u k = Cut t CheckCBN (New (Push u k))

pattern AppXTo :: Trm x i (Dir (Reserve Strat o))
               -> x
               -> Pat i (Cls x i (Dir (Reserve Strat o)) x x) x
               -> Cmd x i (Dir (Reserve Strat o))
pattern AppXTo t x k = Cut t CheckCBN (Dat (Struc (A x :*: k)))

pattern App :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
            -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
            -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern App t u = DoHere (AppTo t u (A HereVar))
                  -- (Cut t CheckCBN (New (A u :*: A HereVar)))

pattern AppX :: Trm (Reserve Label a) i (Dir (Reserve Strat o))
             -> Reserve Label a
             -> Trm (Reserve Label a) i (Dir (Reserve Strat o))
pattern AppX t x = DoHere (AppXTo t x (A (Internal Here)))

pattern DotTo t i k = Cut t CheckCBN (New (i :@: k))

pattern DotTo' :: Trm x i (Dir (Reserve Strat o))
               -> i
               -> Pat i (Cls x i (Dir (Reserve Strat o)) x x) x
               -> Cmd x i (Dir (Reserve Strat o))
pattern DotTo' t i k = Cut t CheckCBN (Dat (Struc (i :@: k)))

pattern Dot :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
            -> i
            -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern Dot t i = DoHere (DotTo t i (A HereVar))
                  -- (Cut t CheckCBN (New (i :@: A HereVar)))

pattern Dot' :: Trm (Reserve Label a) i (Dir (Reserve Strat o))
             -> i
             -> Trm (Reserve Label a) i (Dir (Reserve Strat o))
pattern Dot' t i = DoHere (DotTo' t i (A (Internal Here)))
                   -- (Cut t CheckCBN (Dat (Struc (i :@: A (Internal Here)))))

pattern Obj :: Trm x i o -> Trm x i o
pattern Obj t = New (C t)

pattern Thunk :: Trm x i o -> Trm x i o
pattern Thunk t = Obj t

pattern ForceCxt :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
                 -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern ForceCxt k = Cod [NonRecCoPat (C (Internal It))
                          :=>
                          Cut ItVar CheckCBN k]

pattern ForceTo :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
                -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
                -> Cmd (Reserve Label x) i (Dir (Reserve Strat o))
pattern ForceTo t k = Cut t CheckCBV (ForceCxt k)

pattern Force :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
              -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern Force t = DoHere (ForceTo t HereVar)
  {-
  (Cut
    t
    CheckCBV
    (Cod [NonRecCoPat (C (Internal It))
          :=>
          GoHere ItVar CheckCBN]))
  -}

pattern CallTo :: Trm x i (Dir (Reserve Strat o))
               -> Trm x i (Dir (Reserve Strat o))
               -> Cmd x i (Dir (Reserve Strat o))
pattern CallTo t k = Cut t CheckCBN (Thunk k)

pattern Call :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
             -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern Call t = DoHere (CallTo t HereVar)
                 -- (Cut t CheckCBN (Obj HereVar))

pattern Return :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
               -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern Return t = Cod [NonRecCoPat (C (Internal Here))
                        :=>
                        (Cut t CheckCBV HereVar)]

pattern CompleteObject :: [Rsp (Reserve Label x) i (Dir (Reserve Strat o))]
                       -> Dir (Reserve Strat o)
                       -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern CompleteObject rs a = DoHere (NoOther (GoHere (Cod rs) a))

pattern SelfInCxt :: Trm (Reserve Label x) i (Dir (Reserve Strat o))
                  -> Trm (Reserve Label x) i (Dir (Reserve Strat o))
pattern SelfInCxt k = DoHere (Cut SelfVar CheckCBN k)

-----------------
-- Annotations --
-----------------

pattern CheckCBN, CheckCBV :: Dir (Reserve Strat o)
pattern CheckCBN = Check (Internal CBN)
pattern CheckCBV = Check (Internal CBV)
