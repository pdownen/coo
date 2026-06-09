module Coo.DualCore.Print where

import Coo.DualCore.Syntax

import Data.Bifunctor

import Prettyprinter
import Prettyprinter.Symbols.Unicode

import qualified Data.Map as M

gives = pretty "=>"
takes = pretty "<="
block = align . indent 2
spill = group . hang 2

instance (Pretty x, Pretty i, Pretty o) => Pretty (Trm x i o) where
  pretty (Var x)   = pretty x
  pretty (Act x c) = spill (pretty "do" <+> pretty x <+> gives <+> pretty c)
  pretty (Cod rs)  = pretty "do" <+> braces (prettyList rs)
  pretty (Dat v)   = dGuillemetsOut (pretty v)
  pretty (New p)   = sGuillemetsOut (pretty p)

instance (Pretty x, Pretty i, Pretty o) => Pretty (Cmd x i o) where
  pretty (Cut u o t) = align $ sep
    [ pretty "go" <+> pretty u,
      pretty "as" <+> pretty o,
      pretty "to" <+> pretty t ]

instance (Pretty x, Pretty i, Pretty o) => Pretty (Rsp x i o) where
  pretty (q :=> c) = spill (pretty q <+> gives <> hardline <> pretty c)

  prettyList rs = align $ vsep [ pipe <+> pretty r | r <- rs ]

instance (Pretty i, Pretty c, Pretty a) => Pretty (CoPat i c a) where
  pretty (Nothing :.: p) = pretty p
  pretty (Just x  :.: p) = pretty x <+> pretty "to" <+> pretty p

instance (Pretty i, Pretty c, Pretty a) => Pretty (Pat i c a) where
  pretty = align . prettyComplexPat

prettyBasicPat :: (Pretty i, Pretty c, Pretty a) => Pat i c a -> Doc ann
prettyBasicPat (A a)      = pretty a
prettyBasicPat (C c)      = braces (pretty c)
prettyBasicPat (i :@: MT) = pretty i
prettyBasicPat (i :@: q)  = pretty i <> brackets (prettyComplexPat q)
prettyBasicPat p          = parens (prettyComplexPat p)

prettyComplexPat :: (Pretty i, Pretty c, Pretty a) => Pat i c a -> Doc ann
prettyComplexPat MT         = mempty
prettyComplexPat (p :*: q)  = prettyBasicPat p <> comma <> softline <> prettyComplexPat q
prettyComplexPat p          = prettyBasicPat p

prettyBlankPat :: (Pretty i) => Pat i c a -> Doc ann
prettyBlankPat p = pretty $ bimap (const $ pretty "_") (const $ pretty "_") p

instance (Pretty x, Pretty i, Pretty o, Pretty c, Pretty a) => Pretty (Val x i o c a) where
  pretty (Struc p) = pretty p

prettyShortVal :: (Pretty i, Pretty a, Pretty x, Pretty o, Pretty c)
               => Val x i o c a -> Doc ann
prettyShortVal (Struc p) = pretty $ first blankOut p
  where blankOut (_ :/: _) = pretty "..."
        blankOut c         = pretty c

instance (Pretty x, Pretty i, Pretty o, Pretty c, Pretty a) => Pretty (Cls x i o c a) where
  pretty (Free c)  = pretty c
  pretty (t :/: e) = align (prettyEnv e <> line <> pretty t)

prettyShortCls (t :/: _) = pretty t
prettyShortCls l         = pretty l

prettyEnv :: (Pretty x, Pretty i, Pretty o, Pretty c, Pretty a)
          => Env x i o c a -> Doc ann
prettyEnv e = vsep [ prettyBinding x b <> semi | (x, b) <- M.toList e ]

prettyBinding :: (Pretty x, Pretty i, Pretty o, Pretty c, Pretty a)
              => x -> Bound x i o c a -> Doc ann
prettyBinding x (LetVal o v)
  = hsep [pretty "val", pretty x, colon, pretty o, equals, prettyShortVal v]
prettyBinding x (LetFun o t)
  = hsep [pretty "fun", pretty x, colon, pretty o, equals, prettyShortCls t]

instance (Pretty x, Pretty i, Pretty o, Pretty c, Pretty a) => Pretty (Bound x i o c a) where
  pretty (LetVal o v) = hsep [pretty "val", colon, pretty o, takes, pretty v]
  pretty (LetFun o t) = hsep [pretty "fun", colon, pretty o, gives, pretty t]

instance (Pretty x, Pretty i) => Pretty (Type x i) where
  pretty (TyVar x) = pretty x

instance (Pretty o) => Pretty (Dir o) where
  pretty GoTo      = pretty "⇒"
  pretty ToGo      = pretty "⇐"
  pretty Infer     = mempty
  pretty (Check o) = pretty o

instance Pretty Strat where
  pretty = viaShow
