{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Coo.Source.TypeCheck where

import Coo.Source.Syntax
import Coo.Source.Print ()
import Coo.Source.Polarity (Unified (..))
import Coo.Source.Desugar

import qualified Coo.DualCore.Syntax as DC
import qualified Coo.DualCore.TypeCheck as DC

import qualified Data.Map as M
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Monad.Except

import Prettyprinter

data Extent = Whole | Partial
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Pretty Extent where
  pretty Whole   = pretty "whole"
  pretty Partial = pretty "partial"

instance Semigroup Extent where
  Whole   <> xt = xt
  Partial <> _ = Partial

instance Monoid Extent where
  mempty = Whole

data ElabPole = Strat ::: Type
  deriving (Show, Eq)

instance Pretty ElabPole where
  pretty (s ::: t) = sep [pretty s, colon, pretty t]

data PartialType = Untyped | Typed Type | Illtyped [Type]
  deriving (Show, Eq, Ord)

possibleTypes :: PartialType -> [Type]
possibleTypes Untyped       = []
possibleTypes (Typed t)     = [t]
possibleTypes (Illtyped ts) = ts

forceIlltyped :: PartialType -> PartialType
forceIlltyped = Illtyped . possibleTypes

instance Semigroup PartialType where
  Untyped <> t       = t
  t       <> Untyped = t
  Typed s <> Typed t = case partialUnionTy s t of
    Just r  -> Typed r
    Nothing -> Illtyped [s, t]
  s       <> t       = Illtyped $ possibleTypes s ++ possibleTypes t

instance Monoid PartialType where
  mempty = Untyped

instance Pretty PartialType where
  pretty (Typed t)     = pretty t
  pretty Untyped       = pretty "<unknown type>"
  pretty (Illtyped ts) = pretty "<ill-typed>" <+> pretty ts

data TypeConstraint = Unified Strat ::? PartialType
  deriving (Show, Eq)

instance Semigroup TypeConstraint where
  (s1 ::? t1) <> (s2 ::? t2) = (s1 <> s2) ::? (t1 <> t2)

instance Monoid TypeConstraint where
  mempty = mempty ::? mempty

instance Pretty TypeConstraint where
  pretty (s ::? t) = pretty s <+> colon <+> pretty t

type PrimType = DC.PrimTy CoreId CoreLit

data TyInEnv  = TyIn { typeCxt :: M.Map Variable PrimType,
                       fromCxt :: M.Map Parameter ElabPole }
  deriving (Show)

newtype TyOutEnv = TyOut { toCxt :: M.Map Parameter TypeConstraint }
  deriving (Show)

instance Semigroup TyInEnv where
  env1 <> env2 = TyIn { typeCxt = typeCxt env1 <> typeCxt env2,
                        fromCxt = fromCxt env1 <> fromCxt env2 }

instance Monoid TyInEnv where
  mempty = TyIn mempty mempty

instance Semigroup TyOutEnv where
  TyOut env <> TyOut env' = TyOut $ M.unionWith (<>) env env'

instance Monoid TyOutEnv where
  mempty  = TyOut M.empty
  mconcat = TyOut . M.unionsWith (<>) . fmap toCxt

instance Pretty TyOutEnv where
  pretty (TyOut env) = vsep
    [ pretty x <+> pretty ":" <+> pretty s
    | (x, s) <- M.toList env ]

data TypeError
  = UntypedFunction FunDeclare Reaction
  | UnnamedFunction FunDeclare Reaction
  | MistypedGoTo Term ElabPole ElabPole (Maybe Term)
  | UntypedGoTo Term (Maybe Annotation) (Maybe Term)
  | MispolarTerm Strat Term Strat
  | MistypedTerm ElabPole Term ElabPole
  | UntypedTerm Term
  | MistypedElim Term String Term ElabPole
  | MistypedIntro Term String ElabPole
  | UnhandledTagTerm String Term [(Literal, Type)] Literal
  | UnhandledTagPat Literal Pattern [(Literal, Type)]
  | MistypedPat Pattern Type
  | MistypedCoPatElim CoPattern String CoPattern Type
  | UnhandledTagCoPat CoPattern Literal [(Literal, Type)]
  | MispolarReact Strat Reaction Strat
  | MistypedPop ElabPole Pattern Reaction
  | MistypedProj ElabPole Literal Reaction
  | UnhandledTagReact Literal Reaction [(Literal, Type)] 
  | MistypedVariable ElabPole Parameter ElabPole
  | UntypedVariable Parameter
  | UnknownTypeVar Variable
  | BadPrimTypeLit PrimType Literal
  | UnboundConstraints TyOutEnv
  deriving (Show)

instance Pretty TypeError where
  pretty (UnnamedFunction decl r) = vsep
    [ pretty "No name given for the function definition:",
      indent 4 $ pretty $ LocalFun decl r ]
  pretty (UntypedFunction decl r) = vsep
    [ pretty "No type given for the function definition:",
      indent 4 $ pretty $ LocalFun decl r ]
  pretty (UntypedGoTo u a t) = vsep $
    [ pretty "Cannot infer a type for the go to statement:",
      indent 4 (pretty $ Go u a t) ]
  pretty (UntypedTerm t) = vsep
    [ pretty "Cannot infer the type of the term:",
      indent 4 (pretty t),
      pretty "from its context. (Try giving it a type annotation.)" ]
  pretty (UntypedVariable x) = vsep
    [ pretty "Cannot infer the type of the variable:" <+> pretty x,
      pretty "from its context. (Try giving it a type annotation.)" ]
  pretty (MispolarTerm s1 t s2) = vsep
    [ pretty "Mispolarized term:",
      indent 4 (pretty t),
      pretty "Expected:" <+> pretty s1,
      pretty "Actual:" <+> pretty s2 ]
  pretty (MispolarReact s1 r s2) = vsep
    [ pretty "Mispolarized reaction:",
      indent 4 (pretty r),
      pretty "Expected:" <+> pretty s1,
      pretty "Actual:" <+> pretty s2 ]
  pretty (MistypedGoTo u o1 o2 t) = vsep $
    [ pretty "Mistyped go to statement:",
      indent 4 (pretty $ Go u Nothing t),
      pretty "Go's type:" <+> pretty o1,
      pretty "To's type:" <+> pretty o2 ]
  pretty (MistypedVariable o1 x o2) = vsep
    [ pretty "Mistyped use of variable:" <+> pretty x,
      pretty "Expected:" <+> pretty o1,
      pretty "Actual:" <+> pretty o2 ]
  pretty (MistypedTerm o1 t o2) = vsep
    [ pretty "Mistyped term:",
      indent 4 (pretty t),
      pretty "Expected:" <+> pretty o1,
      pretty "Actual:" <+> pretty o2 ]
  pretty (MistypedPat p t) = vsep
    [ pretty "Mistyped pattern:",
      indent 4 (pretty p),
      pretty "cannot have the expected type",
      indent 4 (pretty t) ]
  pretty (MistypedPop o p r) = vsep
    [ pretty "Mistyped function-argument reaction:",
      indent 4 (pretty $ Pop p r),
      pretty "cannot have the expected type",
      indent 4 (pretty o) ]
  pretty (MistypedProj o i r) = vsep
    [ pretty "Mistyped tag-projection reaction:",
      indent 4 (pretty $ Proj i r),
      pretty "cannot have the expected type",
      indent 4 (pretty o) ]
  pretty (MistypedIntro whole thing o) = vsep
    [ pretty "Mistyped introduction of" <+> pretty thing <+> pretty "in the term",
      indent 4 (pretty whole),
      pretty "which cannot have the expected type",
      indent 4 (pretty o) ]
  pretty (MistypedElim whole use part o) = vsep
    [ pretty "Mistyped" <+> pretty use <+> pretty "of the term",
      indent 4 (pretty part),
      pretty "whose inferred type is",
      indent 4 (pretty o),
      pretty "inside the contex of",
      indent 4 (pretty whole) ]
  pretty (MistypedCoPatElim whole use part o) = vsep
    [ pretty "Mistyped" <+> pretty use <+> pretty "of the copattern",
      indent 4 (pretty part),
      pretty "whose inferred type is",
      indent 4 (pretty o),
      pretty "inside the contex of",
      indent 4 (pretty whole) ]
  pretty (UnhandledTagTerm attempt t table i) = vsep
    [ sep [ pretty "The literal",
            pretty i,
            pretty "is not handled by the tagged type" ],
      indent 4 (pretty $ TagTy table),
      sep [pretty "when trying to", pretty attempt, pretty i, pretty "in the term"],
      indent 4 (pretty t) ]
  pretty (UnhandledTagReact i r table) = vsep
    [ sep [ pretty "The literal",
            pretty i,
            pretty "is not handled by the expected tagged type" ],
      indent 4 (pretty $ TagTy table),
      pretty "of the reaction",
      indent 4 (pretty $ Proj i r) ]
  pretty (UnhandledTagPat i p table) = vsep
    [ sep [ pretty "The literal",
            pretty i,
            pretty "is not handled by the expected tagged type" ],
      indent 4 (pretty $ TagTy table),
      pretty "of the pattern",
      indent 4 (pretty $ Made i p) ]
  pretty (UnhandledTagCoPat q i table) = vsep
    [ sep [ pretty "The literal",
            pretty i,
            pretty "is not handled by the expected tagged type" ],
      indent 4 (pretty $ TagTy table),
      pretty "of the copattern",
      indent 4 (pretty $ q `CoDot` i) ]
  pretty (UnknownTypeVar x) = vsep
    [ pretty "The type variable" <+> pretty x <+> pretty "is not defined in this context." ]
  pretty (BadPrimTypeLit t i) = vsep
    [ sep [ pretty "The literal vaue",
            pretty i,
            pretty "is not a member of the primitive type:",
            pretty t ] ]
  pretty (UnboundConstraints env) = vsep
    [ pretty "Unbound variables used outside of defining context:",
      indent 4 (pretty env) ]

type MonadType m = (MonadReader TyInEnv m, MonadWriter TyOutEnv m, MonadError TypeError m)

type TypeCheckT m = ExceptT TypeError (RWST TyInEnv TyOutEnv () m)

type TypeCheck = TypeCheckT Identity

runTypeCheckT :: Monad m => TypeCheckT m a -> TyInEnv -> m (Either TypeError a, TyOutEnv)
runTypeCheckT m r = do (x, _, out) <- runRWST (runExceptT m) r ()
                       return (x, out)

runTypeCheck :: TypeCheck a -> TyInEnv -> (Either TypeError a, TyOutEnv)
runTypeCheck m r = runIdentity $ runTypeCheckT m r

semiclosedTypeCheck :: (MonadType m) => m a -> m a
semiclosedTypeCheck m = do
  (a, env) <- listen m
  if M.null (toCxt env)
    then return a
    else throwError $ UnboundConstraints env

elaborateAnnote :: Annotation -> Dir ElabPole
elaborateAnnote (Annote (Check s) (Check t)) = Check (s ::: t)
elaborateAnnote (Annote _         GoTo)      = GoTo
elaborateAnnote (Annote _         ToGo)      = ToGo
elaborateAnnote (Annote _         Infer)     = Infer
elaborateAnnote (Annote GoTo      _)         = GoTo
elaborateAnnote (Annote ToGo      _)         = ToGo
elaborateAnnote (Annote Infer     _)         = Infer


unelaborateAnnote :: ElabPole -> Annotation
unelaborateAnnote (s ::: t) = Annote (Check s) (Check t)

elaborateCast :: ElabPole -> TypeCast -> TypeCast
elaborateCast o (PrefixType _)  = PrefixType $ unelaborateAnnote o
elaborateCast o (PostfixType _) = PostfixType $ unelaborateAnnote o

elaborateCmd :: (MonadType m) => Command -> m Command
elaborateCmd [] = do
  expectExtent Partial
  return []
--elaborateCmd [Run u] = do
--  elaborateCmd [Go u Nothing Nothing]
elaborateCmd (s@(Go _ _ _):_) = do
  (s', _) <- elaborateStm s
  return [s']
elaborateCmd (s:c) = do
  (s', env) <- elaborateStm s
  c' <- local (env <>) $ elaborateCmd c
  return (s':c')

elaborateStms :: (MonadType m) => [Statement] -> m ([Statement], TyInEnv)
elaborateStms []    = do
  return ([], mempty)
elaborateStms (s:c) = do
  (s', env) <- elaborateStm s
  (c', env') <- local (env <>) $ elaborateStms c
  return (s':c', env' <> env)

elaborateStm :: (MonadType m) => Statement -> m (Statement, TyInEnv)
elaborateStm s = case s of
  Run t -> do
    (t', _) <- inferTypeTerm t
    return (Run t', mempty)
  LocalFun decl r -> case (extractFunName decl r, decl) of
    (Just name, (_, Just t)) -> do
      let pole = CBN ::: t
      r' <- checkTypeReact Whole pole r
      let env = TyIn mempty $ M.singleton name pole
      return (LocalFun decl r', env)
    (Nothing, _) ->
      throwError $ UnnamedFunction decl r
    (_, (_, Nothing)) ->
      throwError $ UntypedFunction decl r
  SetMatch p u grd els -> do
    (u', s ::: t) <- inferTypeTerm u
    expectTermPolarity CBV u' s
    (p', env) <- checkTypePatBind t p
    (grd', env') <- case grd of
      Nothing  -> return (Nothing, mempty)
      Just cav -> do (cav', _, env') <- inferTypeCaveatBind cav
                     return (Just cav', env')
    els' <- traverse (checkTypeReact Whole (CBN ::: t)) els
    return (SetMatch p' u' grd' els', env' <> env)
  If r -> do
    r' <- checkTypeGuard Partial r
    return (If r', mempty)
  Case u r -> do
    (u', s ::: t) <- inferTypeTerm u
    expectTermPolarity CBV u' s
    r' <- checkTypeReact Partial (CBN ::: t) r
    return (Case u' r', mempty)
  Go u a t -> case elaborateAnnote <$> a of
    Just (Check o) -> do
      u' <- checkTypeTerm o u
      t' <- checkTypeGoToTarget o t
      return (Go u' (Just $ unelaborateAnnote o) t', mempty)
    Just GoTo -> do
      (u', o) <- inferTypeTerm u
      t' <- checkTypeGoToTarget o t
      return (Go u' (Just $ unelaborateAnnote o) t', mempty)
    Just ToGo -> do
      (t', o) <- inferTypeGoToTarget t
      u' <- checkTypeTerm o u
      return (Go u' (Just $ unelaborateAnnote o) t', mempty)
    _ -> do
      left <- tryInferTypeTerm u
      right <- tryInferTypeGoToTarget t
      case (left, right) of
        (Just (u', o1), Just (t', o2))
          | o1 == o2  -> do
              return (Go u' (Just $ unelaborateAnnote o1) (Just t'), mempty)
          | otherwise -> do
              throwError $ MistypedGoTo u' o1 o2 (Just t')
        (Just (u', o), Nothing) -> do
          t' <- checkTypeGoToTarget o t
          return (Go u' (Just $ unelaborateAnnote o) t', mempty)
        (Nothing, Just (t', o)) -> do
          u' <- checkTypeTerm o u
          return (Go u' (Just $ unelaborateAnnote o) (Just t'), mempty)
        (Nothing, Nothing) -> do
          throwError $ UntypedGoTo u Nothing t

isInferrableTerm :: Term -> Bool
isInferrableTerm (App _ _)   = True
isInferrableTerm (Dot _ _)   = True
isInferrableTerm (Call _)    = True
isInferrableTerm (Shift _ t) = isInferrableTerm t
isInferrableTerm _           = False

elaborateTerm :: (MonadType m) => Maybe ElabPole -> Term -> m (Term, ElabPole)
elaborateTerm mo t = case (mo, t) of
  (Just (CBV ::: VarTy x), Make i Nil) -> do
    j <- checkTypePrimLit x i
    return (Make j Nil, CBV ::: VarTy x)
  (_, Var x) -> do
    o' <- elaborateVar mo x
    return (t, o')
  (Nothing, u `App` v) -> do
    (u', o) <- inferTypeTerm u
    (arg, ret) <- case normalizePoleHead o of
      (CBN ::: (arg `PairTy` ret))  -> return (CBV ::: arg, CBN ::: ret)
      _                             -> throwError $ MistypedElim t "function application" u' o
    v' <- checkTypeTerm arg v
    return (u' `App` v', ret)
  (Nothing, u `Dot` i) -> do
    (u', o) <- inferTypeTerm u
    table <- case normalizePoleHead o of
      (CBN ::: TagTy table) -> return table
      _                     -> throwError $ MistypedElim t "projection" u' o
    ret <- case lookup i table of
      Just ty -> return (CBN ::: ty)
      Nothing -> throwError $ UnhandledTagTerm "project" u table i
    return (u' `Dot` i, ret)
  (Just o, Fn r) -> do
    r' <- checkTypeReact Whole o r
    return (Fn r', o)
  (Just o, Do r) -> do
    r' <- checkTypeReact Whole o r
    return (Do r', o)
  (Just o, Nil) -> case normalizePoleHead o of
    (CBV ::: UnitTy) -> return (Nil, o)
    _                -> throwError $ MistypedIntro t "an empty tuple" o
  (Just o, u1 `Pair` u2) -> case normalizePoleHead o of
    (CBV ::: (a1 `PairTy` a2)) -> do
      u1' <- checkTypeTerm (CBV ::: a1) u1
      u2' <- checkTypeTerm (CBV ::: a2) u2
      return ((u1' `Pair` u2'), o)
    _                          -> throwError $ MistypedIntro t "a pair" o
  (Just o, Make i u) -> case normalizePoleHead o of
    (CBV ::: TagTy table)
      | Just a_i <- lookup i table -> do
          u' <- checkTypeTerm (CBV ::: a_i) u
          return (Make i u', o)
      | otherwise -> throwError $ UnhandledTagTerm "make" t table i
    _             -> throwError $ MistypedIntro t "a tagged value" o
  (Just o, Obj u) -> case normalizePoleHead o of
    (CBV ::: ObjTy a) -> do
      u' <- checkTypeTerm (CBN ::: a) u
      return (Obj u', o)
    _                 -> throwError $ MistypedIntro t "a closure value" o
  (Nothing, Obj u) -> do
    (u', s ::: a) <- inferTypeTerm u
    expectTermPolarity CBN u' s
    return (Obj u', CBV ::: ObjTy a)
  (Just o@(s ::: a), Call u) -> do
    expectTermPolarity CBV t s
    u' <- checkTypeTerm (CBN ::: ObjTy a) u
    return (Call u', o)
  (Nothing, Call u) -> do
    (u', o) <- inferTypeTerm u
    o' <- case normalizePoleHead o of
            (CBN ::: ObjTy a) -> return (CBV ::: a)
            _                 -> throwError $ MistypedElim t "strict (!) call" u' o
    return (Call u', o')
  (Just (s ::: a), Shift ps u) -> do
    expectTermPolarity s t (shiftTo ps)
    let isIntro = ps == PS CBV Me || ps == PS CBN You
    a' <- case (isIntro, normalizeTypeHead a) of
            (False, _)       -> return $ ObjTy a
            (True, ObjTy a') -> return a'
            (True, _)        -> throwError $ MistypedIntro t "a shift" (s ::: a)
    u' <- checkTypeTerm (opStrat s ::: a') u
    return (Shift ps u', (shiftTo ps ::: a))
  (Nothing, Shift ps u) -> do
    (u', s ::: a) <- inferTypeTerm u
    expectTermPolarity (opStrat $ shiftTo ps) u s
    let isElim = ps == PS CBV You || ps == PS CBN Me
    a' <- case (isElim, normalizeTypeHead a) of
            (False, _)       -> return $ ObjTy a
            (True, ObjTy a') -> return a'
            _                -> throwError $ MistypedElim t "shift" u (s ::: a)
    return (Shift ps u', (shiftTo ps ::: a'))
  (Nothing, u `AsType` c) -> do
    (u', o) <- elaborateTerm (fromDir $ elaborateAnnote $ castAnnote c) u
    let c' = elaborateCast o c
    return (u' `AsType` c', o)
  (Nothing, Do (Eval u)) -> do
    (u', o) <- inferTypeTerm u
    return (Do (Eval u'), o)
  (Nothing, Do (Exec c)) -> pass $ do
    (c', env) <- listen $ weaken (Implicit Context) $ assignExtent Whole $ elaborateCmd c
    case M.lookup (Implicit Context) (toCxt env) of
      Just (Same s ::? Typed a) -> return ((Do (Exec c'), opStrat s ::: a),
                                           TyOut . M.delete (Implicit Context) . toCxt)
      _                         -> throwError $ UntypedTerm $ Do (Exec c')
  (Nothing, Do (Any x `Rest` Exec c)) -> pass $ do
    (c', env) <- listen $ weaken x $ assignExtent Whole $ elaborateCmd c
    case M.lookup x (toCxt env) of
      Just (Same s ::? Typed a) -> return ((Do (Any x `Rest` Exec c'), opStrat s ::: a),
                                           TyOut . M.delete x . toCxt)
      _                         -> throwError $ UntypedTerm $ Do (Any x `Rest` (Exec c'))
  (Nothing, Do (Any x `Rest` Eval u)) -> pass $ do
    o <- tryInferTypeImplicit Context
    ((u', o'), env) <- listen $ weaken x $ elaborateCoTerm o u
    checkTypeVar o' (Implicit Context)
    case M.lookup x (toCxt env) of
      Just (Same s ::? Typed a) -> return ((Do (Any x `Rest` Eval u'), opStrat s ::: a),
                                           TyOut . M.delete x . toCxt)
      _                         -> throwError $ UntypedTerm $ Do (Any x `Rest` (Eval u))
  (Nothing, Make i Nil)
    | Just a <- inferLiteralBaseType i -> do
        let ann = Annote (Check CBV) (Check a)
        return (t `AsType` PostfixType ann, CBV ::: a)
  (Just o, _) -> do
    (t', o') <- inferTypeTerm t
    if o == o'
      then return (t', o')
      else throwError $ MistypedTerm o t' o'
  (Nothing, _) -> throwError $ UntypedTerm t

inferLiteralBaseType :: Literal -> Maybe Type
inferLiteralBaseType (Int _)  = Just IntTy
inferLiteralBaseType (Flt _)  = Just FloatTy
inferLiteralBaseType (Str _)  = Just StringTy
inferLiteralBaseType TrueTag  = Just BoolTy
inferLiteralBaseType FalseTag = Just BoolTy
inferLiteralBaseType _        = Nothing

checkTypeTerm :: (MonadType m) => ElabPole -> Term -> m Term
checkTypeTerm o t = fst <$> elaborateTerm (Just o) t

inferTypeTerm :: (MonadType m) => Term -> m (Term, ElabPole)
inferTypeTerm = elaborateTerm Nothing

tryInferTypeTerm :: (MonadType m) => Term -> m (Maybe (Term, ElabPole))
tryInferTypeTerm t@(Var x) = do
  cxt <- fromCxt <$> ask
  return $ (t,) <$> M.lookup x cxt
tryInferTypeTerm t
  | isInferrableTerm t = Just <$> inferTypeTerm t
  | otherwise          = return Nothing

elaborateCoTerm :: (MonadType m) => Maybe ElabPole -> CoTerm -> m (CoTerm, ElabPole)
elaborateCoTerm Nothing t = do
  (t', (p' ::: a')) <- elaborateTerm Nothing t
  return (t', (opStrat p' ::: a'))
elaborateCoTerm (Just (p ::: a)) t = do
  (t', (p' ::: a')) <- elaborateTerm (Just (opStrat p ::: a)) t
  return (t', (opStrat p' ::: a'))

inferTypeCoTerm :: (MonadType m) => CoTerm -> m (CoTerm, ElabPole)
inferTypeCoTerm t = do
  (t', (p' ::: a')) <- inferTypeCoTerm t
  return (t', (opStrat p' ::: a'))

checkTypeCoTerm :: (MonadType m) => ElabPole -> CoTerm -> m CoTerm
checkTypeCoTerm (p ::: a) t = checkTypeTerm (opStrat p ::: a) t

tryInferTypeCoTerm :: (MonadType m) => CoTerm -> m (Maybe (CoTerm, ElabPole))
tryInferTypeCoTerm t
  | isInferrableTerm t = Just <$> inferTypeCoTerm t
  | otherwise          = return Nothing

elaborateGoToTarget :: (MonadType m)
                    => Maybe ElabPole -> Maybe CoTerm
                    -> m (Maybe CoTerm, ElabPole)
elaborateGoToTarget o (Just t) = do
  (t', o') <- elaborateCoTerm o t
  return (Just t', o')
elaborateGoToTarget o Nothing = do
  (_, o') <- elaborateCoTerm o (Var (Implicit Context))
  return (Nothing, o')

checkTypeGoToTarget :: (MonadType m) => ElabPole -> Maybe CoTerm -> m (Maybe CoTerm)
checkTypeGoToTarget o t = fst <$> elaborateGoToTarget (Just o) t

inferTypeGoToTarget :: (MonadType m) => Maybe CoTerm -> m (Maybe CoTerm, ElabPole)
inferTypeGoToTarget = elaborateGoToTarget Nothing

tryInferTypeGoToTarget :: (MonadType m) => Maybe CoTerm -> m (Maybe (CoTerm, ElabPole))
tryInferTypeGoToTarget Nothing = return Nothing
tryInferTypeGoToTarget (Just t)
  | isInferrableTerm t = Just <$> inferTypeCoTerm t
  | otherwise          = return Nothing

elaborateVar :: (MonadType m) => Maybe ElabPole -> Parameter -> m ElabPole
elaborateVar p x = do
  cxt <- fromCxt <$> ask
  case (p, M.lookup x cxt) of
    (Just o1,      Just o2)
      | o1 == o2            -> return o1
      | otherwise           -> throwError $ MistypedVariable o1 x o2
    (Nothing,      Just o)  -> return o
    (Just (s:::a), Nothing) -> do tell $ TyOut $ M.singleton x (Same s ::? Typed a)
                                  return (s ::: a)
    (Nothing,      Nothing) -> throwError $ UntypedVariable x

inferTypeVar :: (MonadType m) => Parameter -> m ElabPole
inferTypeVar = elaborateVar Nothing

checkTypeVar :: (MonadType m) => ElabPole -> Parameter -> m Parameter
checkTypeVar p x = do
  _ <- elaborateVar (Just p) x
  return x

tryInferTypeImplicit :: (MonadReader TyInEnv m) => Label -> m (Maybe ElabPole)
tryInferTypeImplicit x = do
  cxt <- ask
  return $ M.lookup (Implicit x) (fromCxt cxt)

checkTypePrimLit :: (MonadReader TyInEnv m, MonadError TypeError m)
                 => Variable -> Literal -> m Literal
checkTypePrimLit x i = do
  cxt <- typeCxt <$> ask
  case M.lookup x cxt of
    Just pty -> case DC.checkPrimPat pty (i DC.:@: DC.MT) of
      Just (j DC.:@: DC.MT) -> return j
      _                     -> throwError $ BadPrimTypeLit pty i
    Nothing  -> throwError $ UnknownTypeVar x

elaborateReact :: (MonadType m) => Reaction -> m Reaction
elaborateReact react = case react of
  Cede ->
    return Cede
  Alt r1 r2 ->
    Alt <$> elaborateReact r1 <*> elaborateReact r2
  Exec c -> do
    cxt_ty <- tryInferTypeImplicit Here
    c' <- case cxt_ty of
      Nothing -> elaborateCmd c
      Just o  -> consumeReactType $ assignType (Implicit Context) o $ elaborateCmd c
    return $ Exec c'
  Eval u -> do
    cxt_ty <- tryInferTypeImplicit Self
    u' <- case cxt_ty of
      Just o  -> consumeReactType $ checkTypeTerm o u
      Nothing -> do
        (s ::: a) <- inferTypeVar (Implicit Context)
        consumeReactType $ checkTypeTerm (opStrat s ::: a) u
    return $ Eval u'
  Else x r -> do
    other_ty <- tryInferTypeImplicit Other
    let o = case other_ty of
              Just o  -> o
              Nothing -> CBN ::: UnitTy
    r' <- assignType x o $ elaborateReact r
    return $ Else x r'
  Rest (Any x) r -> do
    o <- inferTypeVar (Implicit Here)
    r' <- consumeReactType $ assignType x o $ elaborateReact r
    return $ Rest (Any x) r'
  Rest p r -> do
    s ::: a <- inferTypeVar (Implicit Here)
    expectReactPolarity CBN react (opStrat s)
    (p', env) <- checkTypePatBind a p
    r' <- consumeReactType $ local (env <>) $ elaborateReact r
    return $ Rest p' r'
  Rec q r -> do
    s ::: a <- inferTypeVar (Implicit Self)
    expectReactPolarity CBN react s
    (q', b, env) <- inferTypeCoPatBind a q
    r' <- local (env <>) $ assignReactType (CBN ::: b) $ elaborateReact r
    return $ Rec q' r'
  Pop p r -> do
    o <- inferTypeVar (Implicit Self)
    (arg, ret) <- case normalizePoleHead o of
      CBN ::: PairTy arg ret  -> return (arg, ret)
      _                       -> throwError $ MistypedPop o p r
    (p', env) <- checkTypePatBind arg p
    r' <- local (env <>) $ assignReactType (CBN ::: ret) $ elaborateReact r
    return $ Pop p' r'
  Proj i r -> do
    o <- inferTypeVar (Implicit Self)
    a_i <- case normalizePoleHead o of
      CBN ::: TagTy table -> case lookup i table of
        Just a_i          -> return a_i
        Nothing           -> throwError $ UnhandledTagReact i r table
      _                   -> throwError $ MistypedProj o i r
    r' <- assignReactType (CBN ::: a_i) $ elaborateReact r
    return $ Proj i r'
  LetFun decl f r -> case (extractFunName decl r, decl) of
    (Just x, (_, Just t)) -> do
      let pole = CBN ::: t
      f' <- checkTypeReact Whole pole f
      r' <- assignType x pole $ elaborateReact r
      return $ LetFun decl f' r'
    (Nothing, _) ->
      throwError $ UnnamedFunction decl r
    (_, (_, Nothing)) ->
      throwError $ UntypedFunction decl r
  Guard grd t r -> do
    (t', s ::: a) <- inferTypeTerm t
    expectTermPolarity CBV t' s
    (grd', env) <- case grd of
      Just p  -> do (p', env) <- checkTypePatBind a p
                    return (Just p', env)
      Nothing -> do (_, env) <- checkTypePatBind a TruePat
                    return (Nothing, env)
    r' <- local (env <>) $ elaborateReact r
    return $ Guard grd' t' r'

checkTypeReact :: (MonadType m) => Extent -> ElabPole -> Reaction -> m Reaction
checkTypeReact ext o r = assignExtent ext $ assignReactType o $ elaborateReact r

checkTypeGuard :: (MonadType m) => Extent -> Reaction -> m Reaction
checkTypeGuard ext r = assignExtent ext $ consumeReactType $ elaborateReact r

inferTypeCaveatBind :: (MonadType m) => SetCaveat -> m (SetCaveat, ElabPole, TyInEnv)
inferTypeCaveatBind (match, t) = do
  (t', s ::: a) <- inferTypeTerm t
  expectTermPolarity CBV t' s
  (match', env) <- case match of
    Nothing -> return (Nothing, mempty)
    Just p  -> do (p', env) <- checkTypePatBind a p
                  return (Just p', env)
  return ((match', t'), s ::: a, env)

checkTypePatBind :: (MonadReader TyInEnv m, MonadError TypeError m)
                 => Type -> Pattern -> m (Pattern, TyInEnv)
checkTypePatBind t p = case (normalizeTypeHead t, p) of
  (VarTy x,        Made i IsNil)   -> do
    j <- checkTypePrimLit x i
    return (Made j IsNil, mempty)
  (_,              Any x)          -> do
    return (Any x, TyIn mempty $ M.singleton x (CBV ::: t))
  (ObjTy t',       IsObj x)        -> do
    return (IsObj x, TyIn mempty $ M.singleton x (CBN ::: t'))
  (UnitTy,         IsNil)          -> do
    return (IsNil, mempty)
  (t1 `PairTy` t2, p1 `IsPair` p2) -> do
    (p1', env1) <- checkTypePatBind t1 p1
    (p2', env2) <- checkTypePatBind t2 p2
    return (p1' `IsPair` p2', env2 <> env1)
  (TagTy table,    Made i p_i)     -> case lookup i table of
    Just t_i -> do (p_i', env) <- checkTypePatBind t_i p_i
                   return (Made i p_i', env)
    Nothing  -> throwError $ UnhandledTagPat i p_i table
  _                                -> throwError $ MistypedPat p t

inferTypeCoPatBind :: (MonadReader TyInEnv m, MonadError TypeError m)
                   => Type -> CoPattern -> m (CoPattern, Type, TyInEnv)
inferTypeCoPatBind t copat = case copat of
  SelfIs x -> return (SelfIs x, t, TyIn mempty $ M.singleton x (CBN ::: t))
  q `CoApp` p -> do
    (q', t', env') <- inferTypeCoPatBind t q
    (arg, ret) <- case normalizeTypeHead t' of
      (arg `PairTy` ret)  -> return (arg, ret)
      _                   -> throwError $ MistypedCoPatElim q "function application" q' t'
    (p', env) <- checkTypePatBind arg p
    return (q' `CoApp` p', ret, env <> env')
  q `CoDot` i -> do
    (q', t', env') <- inferTypeCoPatBind t q
    table <- case normalizeTypeHead t' of
      (TagTy table) -> return table
      _             -> throwError $ MistypedCoPatElim q "projection" q' t'
    ret <- case lookup i table of
      Just ty -> return ty
      Nothing -> throwError $ UnhandledTagCoPat q' i table
    return (q' `CoDot` i, ret, env')

assignType :: (MonadReader TyInEnv m)
           => Parameter -> ElabPole -> m a -> m a
assignType x o = local (\env -> env{fromCxt = M.insert x o $ fromCxt env})

weaken :: (MonadReader TyInEnv m) => Parameter -> m a -> m a
weaken x = local (\env -> env{fromCxt = M.delete x $ fromCxt env})

extentEnv :: Extent -> TyInEnv
extentEnv Whole   = mempty
extentEnv Partial = TyIn mempty $ M.singleton (Implicit Join) (CBN ::: UnitTy)

assignExtent :: (MonadReader TyInEnv m) => Extent -> m a -> m a
assignExtent Whole   = weaken (Implicit Join)
assignExtent Partial = assignType (Implicit Join) (CBN ::: UnitTy)

expectExtent :: (MonadType m) => Extent -> m ()
expectExtent Whole   = return ()
expectExtent Partial = do
  _ <- checkTypeVar (CBN ::: UnitTy) (Implicit Join)
  return ()

assignReactType :: (MonadReader TyInEnv m) => ElabPole -> m a -> m a
assignReactType o@(s ::: a) = assignType (Implicit Self) o
                            . assignType (Implicit Other) o
                            . assignType (Implicit Here) (s' ::: a)
  where s' = opStrat s

consumeReactType :: (MonadReader TyInEnv m) => m a -> m a
consumeReactType = weaken (Implicit Self)
                 . weaken (Implicit Other)
                 . weaken (Implicit Here)

assignPatType :: (MonadReader TyInEnv m, MonadError TypeError m)
              => Type -> Pattern -> m a -> m a
assignPatType t p m = do
  (_, bind) <- checkTypePatBind t p
  local (bind <>) m

assignCoPatType :: (MonadReader TyInEnv m, MonadError TypeError m)
                => Type -> CoPattern -> (Type -> m a) -> m a
assignCoPatType t q m = do
  (_, t', bind) <- inferTypeCoPatBind t q
  local (bind <>) (m t')

expectTermPolarity :: (MonadError TypeError m) => Strat -> Term -> Strat -> m ()
expectTermPolarity expected term actual
  | expected == actual = return ()
  | otherwise          = throwError $ MispolarTerm expected term actual

expectReactPolarity :: (MonadError TypeError m) => Strat -> Reaction -> Strat -> m ()
expectReactPolarity expected react actual
  | expected == actual = return ()
  | otherwise          = throwError $ MispolarReact expected react actual


normalizePoleHead :: ElabPole -> ElabPole
normalizePoleHead (s ::: t) = s ::: normalizeTypeHead t

normalizeTypeHead :: Type -> Type
normalizeTypeHead (s `ArrowTy` t) = s `PairTy` t
normalizeTypeHead (s `ArrDoTy` t) = s `PairTy` (ObjTy t)
normalizeTypeHead t               = t


partialUnionTy :: Type -> Type -> Maybe Type
partialUnionTy s t = case (normalizeTypeHead s, normalizeTypeHead t) of
  (VarTy x, VarTy y)
    | x == y ->
      Just $ VarTy y
  (ObjTy s, ObjTy t)
    -> ObjTy <$> partialIntersectTy s t
  (UnitTy, UnitTy) ->
    Just UnitTy
  (s1 `PairTy` s2, t1 `PairTy` t2) ->
    PairTy <$> partialUnionTy s1 t1 <*> partialUnionTy s2 t2
  (TagTy xss, TagTy yts) ->
    TagTy <$> combine xss yts
    where combine []            yts = Just yts
          combine ((x,s_x):xss) yts
            | Just (t_x, yts') <- extractTaggedType x yts = do
                st_x <- partialUnionTy s_x t_x
                table <- combine xss yts'
                return ((x, st_x) : table)
            | otherwise = ((x,s_x) :) <$> combine xss yts
  _ -> Nothing

partialIntersectTy :: Type -> Type -> Maybe Type
partialIntersectTy s t = case (normalizeTypeHead s, normalizeTypeHead t) of
  (VarTy x, VarTy y)
    | x == y ->
      Just $ VarTy y
  (ObjTy s, ObjTy t)
    -> ObjTy <$> partialUnionTy s t
  (UnitTy, UnitTy) ->
    Just UnitTy
  (s1 `PairTy` s2, t1 `PairTy` t2) ->
    PairTy <$> partialIntersectTy s1 t1 <*> partialIntersectTy s2 t2
  (TagTy xss, TagTy yts) ->
    Just $ TagTy $ common xss yts
    where common []            _   = []
          common ((x,s_x):xss) yts
            | Just a <- x_ty = a : common xss yts
            | otherwise      = common xss yts
            where x_ty = do t_x <- lookup x yts
                            st_x <- partialIntersectTy s_x t_x
                            return (x, st_x)
  _ -> Nothing

extractTaggedType :: Literal -> [(Literal, Type)] -> Maybe (Type, [(Literal, Type)])
extractTaggedType i (a@(j,t):tys)
  | i == j                                     = Just (t, tys)
  | Just (t', tys') <- extractTaggedType i tys = Just (t', (a:tys'))
extractTaggedType _ _                          = Nothing
