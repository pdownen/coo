module Coo.Source.Print where

import Coo.Source.Syntax
import Data.Maybe
import qualified Data.Text as Txt
import Prettyprinter

gives = pretty "=>"
takes = pretty "<="
block = align
spill = group . hang 2

instance Pretty Label where
  pretty Here      = pretty "here"
  pretty Join      = pretty "join"
  pretty Self      = pretty "self"
  pretty Other     = pretty "other"
  pretty Context   = pretty "context"
  pretty Unmatched = pretty "unmatched"

instance Pretty Parameter where
  pretty (Bound x)    = pretty x
  pretty (Unbound x)  = pretty x
  pretty (Implicit x) = pretty "\\" <> pretty x

instance Pretty Literal where
  pretty (Int n) = pretty n
  pretty (Flt n) = pretty n
  pretty (Str s) = pretty (show s)
  pretty (Tag x) = pretty x

instance Pretty Statement where
  pretty (Run t)        = pretty t
  pretty (Go v a t)     = sep $ catMaybes
    [ Just $ pretty "go" <+> pretty v,
      (pretty "as" <+>) <$> fmap pretty a,
      (pretty "to" <+>) <$> fmap pretty t ]
  pretty (LocalFun d r) = prettyFunDeclare d $ pretty "fun" <+> align (prettyReact RecMode r)
  pretty (If r)         = pretty "if" <+> align (prettyReact GuardMode r)
  pretty (Case t r)     = align $ vsep [ pretty "match" <+> pretty t <+> pretty "with",
                                         align (prettyReact WholeMode r) ]
  pretty (SetMatch p t grd els)
    = align $ vsep $ catMaybes
      [ Just $ pretty "val" <+> prettyComplexPat p <+> pretty "=" <+> pretty t,
        (pretty "if" <+>) <$> fmap (align . prettyCaveat) grd,
        (pretty "else" <+>) <$> fmap (align . prettyReact WholeMode) els ]

  -- pretty-printing Command = [Statement]
  prettyList cs = align $ vsep $ fmap pretty cs

prettyFunDeclare :: FunDeclare -> Doc ann -> Doc ann
prettyFunDeclare (Nothing, Nothing) body = body
prettyFunDeclare (x,       t)       body = align $ vsep
  [pretty "fun" <+> pretty x <+> colon <+> pretty t, body]

prettyCaveat :: SetCaveat -> Doc ann
prettyCaveat (pat, chk) = prettyReact GuardMode $ Guard pat chk Cede

instance Pretty Term where
  pretty = prettyComplexTerm

prettyBasicTerm :: Term -> Doc ann
prettyBasicTerm t0 = case t0 of
  Var x          -> pretty x
  Obj t          -> braces (prettyComplexTerm t)
  Make (Tag s) Nil
    | Txt.null s -> pretty "[]"
  Make i Nil     -> pretty i
  Make i t       -> pretty i <> brackets (prettyComplexTerm t)
  t              -> parens (prettyComplexTerm t)

prettyNeutralTerm :: Term -> Doc ann
prettyNeutralTerm t0 = case t0 of
  t `App` Call u           -> prettyNeutralTerm t <+> pretty "!" <+> prettyComplexTerm u
  t `App`  u               -> prettyNeutralTerm t <+> prettyBasicTerm u
  t `Dot`  i               -> prettyNeutralTerm t <+> dot <> pretty i
  t `AsType` PostfixType a -> prettyNeutralTerm t <+> colon <+> pretty a
  t                        -> prettyBasicTerm t

prettyComplexTerm :: Term -> Doc ann
prettyComplexTerm t0 = case t0 of
  Nil                     -> mempty
  t `Pair` u              -> prettyNeutralTerm t <> comma <+> prettyComplexTerm u
  Do r                    -> pretty "do" <+> prettyReact WholeMode r
  Fn r                    -> pretty "fn" <+> prettyReact LamMode r
  Call t                  -> pretty "!" <+> prettyNeutralTerm t
  Shift ps t              -> pretty ps <+> prettyNeutralTerm t
  AsType t (PrefixType a) -> pretty a <> pretty "::" <> prettyNeutralTerm t
  t                       -> prettyNeutralTerm t

instance Pretty Reaction where
  pretty = prettyReact UnknownMode
    

gatherReacts :: Reaction -> [Reaction]
gatherReacts Cede         = []
gatherReacts (r `Alt` rs) = r : gatherReacts rs
gatherReacts r            = [r]

data ReactionMode = UnknownMode | WholeMode | LamMode | RecMode | GuardMode
  deriving (Show, Eq, Ord, Enum, Bounded)

prettyReact :: ReactionMode -> Reaction -> Doc ann
prettyReact _ (Eval t)    = gives <+> spill (pretty t)
prettyReact _ (Exec c)    = gives <+> block (pretty c)
prettyReact _ Cede        = mempty
prettyReact m r@(Alt _ _) = align $ vsep [ pipe <+> prettyReact m r' | r' <- rs ]
  where rs = gatherReacts r

prettyReact WholeMode (p `Rest` r) = pretty p <+> prettyReact WholeMode r
prettyReact _         r@(Rest _ _) = pretty "with" <+> prettyReact WholeMode r

prettyReact LamMode (p `Pop`  r) = prettyBasicPat p <+> prettyReact LamMode r
prettyReact LamMode (i `Proj` r) = dot <> pretty i <+> prettyReact LamMode r
prettyReact _       r@(Pop  _ _) = pretty "of" <+> prettyReact LamMode r
prettyReact _       r@(Proj _ _) = pretty "of" <+> prettyReact LamMode r

prettyReact RecMode (q `Rec` (p `Rest` r))
  = pretty "go" <+> pretty q <+> pretty "to" <+> pretty p <+> prettyReact WholeMode r
prettyReact RecMode (q `Rec` r@(Rec _ _))
  = pretty q <+> pretty "as" <+> prettyReact RecMode r
prettyReact RecMode (q `Rec` r)
  = pretty q <+> prettyReact RecMode r
prettyReact _       r@(Rec _ _)
  = pretty "where" <+> prettyReact RecMode r

prettyReact GuardMode (Guard Nothing  t r)
  = pretty t <+> prettyReact GuardMode r
prettyReact GuardMode (Guard (Just p) t r)
  = pretty p <+> takes <+> pretty t <+> prettyReact GuardMode r
prettyReact _         r@(Guard _ _ _)
  = pretty "if" <+> prettyReact GuardMode r

prettyReact _ (LetFun d f r)
  = align $ vsep [ prettyFunDeclare d $ pretty "fun" <+> prettyReact RecMode f,
                   prettyReact UnknownMode r ]

prettyReact _ (Else p r)
  = pretty "else" <+> pretty p <+> prettyReact UnknownMode r


instance Pretty Pattern where
  pretty = prettyBasicPat

prettyBasicPat :: Pattern -> Doc ann
prettyBasicPat (Any x)        = pretty x
prettyBasicPat (Made i IsNil) = pretty i
prettyBasicPat (Made i p)     = pretty i <> brackets (group $ prettyComplexPat p)
prettyBasicPat (IsObj x)      = braces (pretty x)
prettyBasicPat p              = parens (group $ prettyComplexPat p)

prettyComplexPat :: Pattern -> Doc ann
prettyComplexPat (p `IsPair` q) = pretty p <> comma <+> prettyComplexPat q
prettyComplexPat IsNil          = mempty
prettyComplexPat p              = pretty p

instance Pretty CoPattern where
  pretty (SelfIs x)    = pretty x
  pretty (q `CoApp` p) = pretty q <+> pretty p
  pretty (q `CoDot` i) = pretty q <+> dot <> pretty i

instance Pretty Declaration where
  pretty (Field p t)    = pretty "val" <+> pretty p <+> takes <+> pretty t
  pretty (Function d r) = prettyFunDeclare d $ pretty "fun" <+> prettyReact RecMode r

  -- pretty-printing Bindings = [Declaration]
  prettyList ds = vsep [ pretty d <> semi | d <- ds ]

instance Pretty Module where
  pretty (Package ds t) = prettyList ds <> line <> pretty t

instance Pretty Annotation where
  pretty (Annote (Check p) (Check t)) = pretty p <+> colon <+> pretty t
  pretty (Annote Infer     (Check t)) = pretty t
  pretty (Annote (Check p) Infer)     = pretty p
  pretty (Annote Infer     Infer)     = mempty
  pretty (Annote p         t)         = pretty p <+> colon <+> pretty t

instance (Pretty a) => Pretty (Dir a) where
  pretty GoTo      = pretty "⇒"
  pretty ToGo      = pretty "⇐"
  pretty Infer     = pretty ""
  pretty (Check a) = pretty a

instance Pretty Strat where
  pretty = viaShow

instance Pretty Who where
  pretty = viaShow

instance Pretty PolarityShift where
  pretty (PS CBN Me)  = pretty "↑"
  pretty (PS CBN You) = pretty "⇑"
  pretty (PS CBV Me)  = pretty "↓"
  pretty (PS CBV You) = pretty "⇓"

instance Pretty Type where
  pretty = prettyComplexTy

prettyBasicTy t = case t of
  VarTy x   -> pretty x
  ObjTy t   -> braces $ pretty t
  TagTy xts -> encloseSep
    (pretty "[ ") (pretty " ]") (flatAlt (pretty "| ") (pretty " | "))
    [ prettyTagTy x t | (x, t) <- xts ]
  _         -> parens $ prettyComplexTy t

prettyComplexTy t = case t of
--  RecTy x t   -> pretty "rec" <+> pretty x <+> equals <+> prettyComplexTy t
  UnitTy      -> mempty
  PairTy s t  -> prettyBasicTy s <> comma <+> prettyComplexTy t
  ArrowTy s t -> prettyBasicTy s <+> pretty "->" <+> prettyComplexTy t
  ArrDoTy s t -> prettyBasicTy s <+> pretty "~>" <+> prettyComplexTy t
  _           -> prettyBasicTy t

prettyTagTy x UnitTy = pretty x
prettyTagTy x t      = pretty x <+> colon <+> prettyComplexTy t
  
