{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
module Coo.DualCore.TypeCheck where

import Coo.DualCore.Syntax
import Coo.DualCore.Print ()
import Coo.DualCore.Polarity (Unified (..))
import Coo.Data.Namespace

import qualified Data.Text as Txt
import qualified Data.Map as M
import Data.Bitraversable
-- import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.RWS
import Control.Monad.Writer

import Prettyprinter

data ElabPole x i = Strat ::: Type x i
  deriving (Show, Eq)

data TyGoal x i = Strat ::! TyAnn x i
  deriving (Show, Eq)

type UnelabPole x i = Dir (TyGoal x i)

type ElabNewPat   x i = Pat i (Trm x i (ElabPole x i)) (Trm x i (ElabPole x i))
type UnelabNewPat x i = Pat i (Trm x i (UnelabPole x i)) (Trm x i (UnelabPole x i))

instance (Pretty x, Pretty i) => Pretty (ElabPole x i) where
  pretty (s ::: t) = sep [pretty s, colon, pretty t]

instance (Pretty x, Pretty i) => Pretty (TyGoal x i) where
  pretty (s ::! a) = sep [pretty s, colon, pretty a]

data PartialType x i = Untyped | Typed (Type x i) | Illtyped [Type x i]
  deriving (Show, Eq, Ord)

possibleTypes :: PartialType x i -> [Type x i]
possibleTypes Untyped       = []
possibleTypes (Typed t)     = [t]
possibleTypes (Illtyped ts) = ts

forceIlltyped :: PartialType x i -> PartialType x i
forceIlltyped = Illtyped . possibleTypes

instance (Ord x, Ord i) => Semigroup (PartialType x i) where
  Untyped <> t       = t
  t       <> Untyped = t
  Typed s <> Typed t = case partialUnionTy s t of
    Just r  -> Typed r
    Nothing -> Illtyped [s, t]
  s       <> t       = Illtyped $ possibleTypes s ++ possibleTypes t

instance (Ord x, Ord i) => Monoid (PartialType x i) where
  mempty = Untyped

instance (Pretty x, Pretty i) => Pretty (PartialType x i) where
  pretty (Typed t)     = pretty t
  pretty Untyped       = pretty "<unknown type>"
  pretty (Illtyped ts) = pretty "<ill-typed>" <+> pretty ts

data TypeConstraint x i = Unified Strat ::? PartialType x i
  deriving (Show, Eq)

instance (Ord x, Ord i) => Semigroup (TypeConstraint x i) where
  (s1 ::? t1) <> (s2 ::? t2) = (s1 <> s2) ::? (t1 <> t2)

instance (Ord x, Ord i) => Monoid (TypeConstraint x i) where
  mempty = mempty ::? mempty

instance (Pretty x, Pretty i) => Pretty (TypeConstraint x i) where
  pretty (s ::? t) = pretty s <+> colon <+> pretty t

data PrimTy x i = PrimTy {
  primTyName :: Txt.Text,
  checkPrimPat :: forall c a. Pat i c a -> Maybe (Pat i (Type x i, c) (Type x i, a)) }

instance Show (PrimTy x i) where
  show = Txt.unpack . primTyName

instance Pretty (PrimTy x i) where

data TyInEnv x i = TyIn { typeCxt :: M.Map x (PrimTy x i),
                          fromCxt :: M.Map x (ElabPole x i) }

newtype TyOutEnv x i = TyOut { toCxt :: M.Map x (TypeConstraint x i) }
  deriving (Show, Eq)

instance (Ord x) => Semigroup (TyInEnv x i) where
  env <> env' = TyIn { fromCxt = fromCxt env <> fromCxt env',
                       typeCxt = typeCxt env <> typeCxt env' }

instance (Ord x) => Monoid (TyInEnv x i) where
  mempty = TyIn mempty mempty

instance (Ord x, Ord i) => Semigroup (TyOutEnv x i) where
  TyOut env <> TyOut env' = TyOut $ M.unionWith (<>) env env'

instance (Ord x, Ord i) => Monoid (TyOutEnv x i) where
  mempty  = TyOut M.empty
  mconcat = TyOut . M.unionsWith (<>) . fmap toCxt

instance (Pretty x, Pretty i) => Pretty (TyOutEnv x i) where
  pretty env = vsep
    [ pretty x <+> pretty ":" <+> pretty s
    | (x, s) <- M.toList $ toCxt env ]

instance (Pretty x, Pretty i) => Pretty (TyInEnv x i) where
  pretty env = vsep
    [ pretty x <+> pretty ":" <+> pretty s
    | (x, s) <- M.toList $ fromCxt env ]

data TypeError x i
  = MistypedCommand (ElabPole x i) (Cmd x i (UnelabPole x i)) (ElabPole x i)
  | MispolarTerm Strat (Trm x i (UnelabPole x i)) Strat
  | UntypedTerm (Trm x i (UnelabPole x i))
  | MistypedVariable (ElabPole x i) x (ElabPole x i)
  | UntypedVariable x
  | MistypedAction [Type x i] x (Cmd x i (ElabPole x i))
  | MispolarAction x (Cmd x i (ElabPole x i))
  | UntypedAction x (Cmd x i (ElabPole x i))
  | TypePatternMismatch (Type x i) (GenericPat i)
  | TagTypeUnhandled i (M.Map i (Type x i))
  | UnannotatedBinding (Bound x i (UnelabPole x i) x x)
  | UnknownTypeVar x
  | BadPrimTypePat (PrimTy x i) (GenericPat i)
  | UnboundConstraints (TyOutEnv x i)
  deriving (Show)

instance (Pretty x, Pretty i) => Pretty (TypeError x i) where
  pretty (MistypedCommand o1 c o2) = vsep
    [ pretty "Mistyped command:",
      indent 4 (pretty c),
      pretty "Go's type:" <+> pretty o1,
      pretty "To's type:" <+> pretty o2 ]
  pretty (MispolarTerm s1 t s2) = vsep
    [ pretty "Mispolarized term:",
      indent 4 (pretty t),
      pretty "Expected:" <+> pretty s1,
      pretty "Actual:" <+> pretty s2 ]
  pretty (UntypedTerm t) = vsep
    [ pretty "Cannot infer the type of the term:",
      indent 4 (pretty t),
      pretty "from its context. (Try giving it a type annotation.)" ]
  pretty (MistypedVariable o1 x o2) = vsep
    [ sep [pretty "Variable", pretty x, pretty "used with the wrong type."],
      pretty "Expected:" <+> pretty o1,
      pretty "Actual:" <+> pretty o2 ]
  pretty (UntypedVariable x) = vsep
    [ pretty "Untyped variable" <+> pretty x <+> pretty "cannot be inferred.",
      pretty "(Try giving it a type annotation at its binding or use sites.)"]
  pretty (MistypedAction ts x c) = vsep
    [ sep [pretty "Inconsistent uses of variable", pretty x, pretty "at types",  colon],
      indent 4 $ align $ vsep $ pretty <$> ts,
      pretty "inferred from the command",
      indent 4 $ pretty c ]
  pretty (MispolarAction x c) = vsep
    [ sep [ pretty "Inconsistent uses of variable",
            pretty x,
            pretty "as both a function and value" ],
      pretty "inferred from the command",
      indent 4 $ pretty c ]
  pretty (UntypedAction x c) = vsep
    [ sep [ pretty "Cannot infer the type of", pretty x, pretty "from the command:" ],
      indent 4 $ pretty c,
      pretty "(Is it even used? Try giving it a type annotation.)"]
  pretty (TypePatternMismatch t p) = vsep
    [ pretty "The pattern",
      indent 4 $ pretty p,
      pretty "cannot have the type",
      indent 4 $ pretty t ]
  pretty (TagTypeUnhandled i table) = vsep
    [ pretty "The tag" <+> pretty i <+> pretty "is not described by the type",
      indent 4 $ pretty $ TagTy table ]
  pretty (UnannotatedBinding b) = vsep
    [ pretty "No type annotation given in the binding",
      indent 4 $ pretty b ]
  pretty (UnknownTypeVar x) = vsep
    [ pretty "The type variable" <+> pretty x <+> pretty "is not defined in this context."]
  pretty (BadPrimTypePat t p) = vsep
    [ pretty "The primitive type" <+> pretty t <+> pretty "is incompatible with the pattern:",
      indent 4 $ pretty p ]
  pretty (UnboundConstraints env) = vsep
    [ pretty "Unbound variables used outside of defining context:",
      indent 4 (pretty env) ]

type MonadType x i m = (MonadReader (TyInEnv x i) m,
                        MonadWriter (TyOutEnv x i) m,
                        MonadError (TypeError x i) m)

type TypeCheckT x i m = ExceptT (TypeError x i) (RWST (TyInEnv x i) (TyOutEnv x i) () m)

type TypeCheck x i = TypeCheckT x i Identity

runTypeCheckT :: Monad m
              => TypeCheckT x i m a -> TyInEnv x i
              -> m (Either (TypeError x i) a, TyOutEnv x i)
runTypeCheckT m r = do (x, _, out) <- runRWST (runExceptT m) r ()
                       return (x, out)

runTypeCheck :: TypeCheck x i a -> TyInEnv x i
             -> (Either (TypeError x i) a, TyOutEnv x i)
runTypeCheck m r = runIdentity $ runTypeCheckT m r

semiclosedTypeCheck :: (MonadType x i m) => m a -> m a
semiclosedTypeCheck m = do
  (a, env) <- listen m
  if M.null (toCxt env)
    then return a
    else throwError $ UnboundConstraints env

elaborateCmd :: (MonadType x i m, Ord x, Ord i)
             => Cmd x i (UnelabPole x i)
             -> m (Cmd x i (ElabPole x i))
elaborateCmd c@(Cut u p t) = case p of
  Check o -> do
    o' <- normalizePole o
    Cut <$> checkTypeTrm o' u <*> pure o' <*> checkTypeCoTrm o' t
  GoTo    -> do (u', o) <- inferTypeTrm u
                t' <- checkTypeCoTrm o t
                return $ Cut u' o t'
  ToGo    -> do (t', o) <- inferTypeCoTrm t
                u' <- checkTypeTrm o u
                return $ Cut u' o t'
  Infer   -> do (u', o1) <- inferTypeTrm u
                (t', o2) <- inferTypeCoTrm t
                if o1 == o2
                  then return $ Cut u' o1 t'
                  else throwError $ MistypedCommand o1 c o2

elaborateTrm :: (MonadType x i m, Ord x, Ord i)
             => Maybe (ElabPole x i)
             -> Trm x i (UnelabPole x i)
             -> m (Trm x i (ElabPole x i), ElabPole x i)
elaborateTrm (Just o@(s ::: a)) t@(New p) = do
  expectPolarity s CBV t
  p' <- checkTypeNewPat a p
  return (New p', o)
elaborateTrm (Just o@(s ::: a)) t@(Dat v) = do
  expectPolarity s CBV t
  v' <- checkTypeVal a v
  return (Dat v', o)
elaborateTrm (Just o@(s ::: a)) t@(Cod rs) = do
  expectPolarity s CBN t
  rs' <- checkTypeRsps a rs
  return (Cod rs', o)
elaborateTrm p (Var x) = do
  o <- elaborateVar p x
  return (Var x, o)
elaborateTrm (Just o@(s ::: a)) (Act x c) = do
  c' <- assignType x (opp s ::: a) $ elaborateCmd c
  return (Act x c', o)
elaborateTrm Nothing (Act x c) = pass $ do
  (c', env) <- listen $ weaken x $ elaborateCmd c
  case M.lookup x (toCxt env) of
    Just (Same s ::? Typed a) -> do
      let unbind = TyOut . M.delete x . toCxt
      return ((Act x c', (opp s ::: a)), unbind)
    Just (Conflict ::? _) ->
      throwError $ MispolarAction x c'
    Just (_ ::? Illtyped as) ->
      throwError $ MistypedAction as x c'
    _ ->
      throwError $ UntypedAction x c'
elaborateTrm Nothing t = throwError $ UntypedTerm t
-- The following case is redundant:
-- elaborateTrm (Just o) t          = do
--   r@(t', o') <- inferTypeTrm t
--   same <- o == o'
--   if same
--     then return r
--     else throwError $ MistypedTerm o t' o'

inferTypeTrm :: (MonadType x i m, Ord x, Ord i)
             => Trm x i (UnelabPole x i)
             -> m (Trm x i (ElabPole x i), ElabPole x i)
inferTypeTrm = elaborateTrm Nothing

checkTypeTrm :: (MonadType x i m, Ord x, Ord i)
             => ElabPole x i
             -> Trm x i (UnelabPole x i)
             -> m (Trm x i (ElabPole x i))
checkTypeTrm o t = fst <$> elaborateTrm (Just o) t

elaborateCoTrm :: (MonadType x i m, Ord x, Ord i)
               => Maybe (ElabPole x i)
               -> CoTrm x i (UnelabPole x i)
               -> m (CoTrm x i (ElabPole x i), ElabPole x i)
elaborateCoTrm Nothing t = do
  (t', (p' ::: a')) <- elaborateTrm Nothing t
  return (t', (opp p' ::: a'))
elaborateCoTrm (Just (p ::: a)) t = do
  (t', (p' ::: a')) <- elaborateTrm (Just (opp p ::: a)) t
  return (t', (opp p' ::: a'))

inferTypeCoTrm :: (MonadType x i m, Ord x, Ord i)
               => CoTrm x i (UnelabPole x i)
               -> m (CoTrm x i (ElabPole x i), ElabPole x i)
inferTypeCoTrm t = do
  (t', (p ::: a)) <- inferTypeTrm t
  return (t', (opp p ::: a))

checkTypeCoTrm :: (MonadType x i m, Ord x, Ord i)
               => ElabPole x i
               -> CoTrm x i (UnelabPole x i)
               -> m (CoTrm x i (ElabPole x i))
checkTypeCoTrm (p ::: a) t = checkTypeTrm (opp p ::: a) t


elaborateVar :: (MonadType x i m, Ord x, Ord i)
             => Maybe (ElabPole x i) -> x -> m (ElabPole x i)
elaborateVar p x = do
  cxt <- fromCxt <$> ask
  case (p, M.lookup x cxt) of
    (Just o1, Just o2) -> do
      if o1 == o2
        then return o1
        else throwError $ MistypedVariable o1 x o2
    (Nothing,    Just o)    -> return o
    (Just (s:::a), Nothing) -> do tell $ TyOut $ M.singleton x (Same s ::? Typed a)
                                  return (s ::: a)
    (Nothing,    Nothing)   -> throwError $ UntypedVariable x

inferTypeVar :: (MonadType x i m, Ord x, Ord i)
             => x -> m (ElabPole x i)
inferTypeVar = elaborateVar Nothing

checkTypeVar :: (MonadType x i m, Ord x, Ord i)
             => ElabPole x i -> x -> m x
checkTypeVar o x = do
  elaborateVar (Just o) x
  return x


checkTypePat :: (Ord x, Ord i,
                 MonadError (TypeError x i) m,
                 MonadReader (TyInEnv x i) m)
             => (Type x i -> c -> m c')
             -> (Type x i -> a -> m a')
             -> Type x i -> Pat i c a -> m (Pat i c' a')
checkTypePat cod dat t p = do
  case (t, p) of
    (_, A a) ->
      A <$> dat t a
    (ObjTy t, C c) ->
      C <$> cod t c
    (UnitTy, MT) ->
      return MT
    (t1 `PairTy` t2, p1 :*: p2) ->
      (:*:) <$> checkTypePat cod dat t1 p1 <*> checkTypePat cod dat t2 p2
    (TagTy table, j :@: q) -> case M.lookup j table of
      Just t' -> (j :@:) <$> checkTypePat cod dat t' q
      Nothing -> throwError $ TagTypeUnhandled j table
    (VarTy (External x), _) -> do
      cxt <- typeCxt <$> ask
      case M.lookup x cxt of
        Just pty -> case checkPrimPat pty p of
                      Just p' -> bitraverse (uncurry cod) (uncurry dat) p'
                      Nothing -> throwError $ BadPrimTypePat pty (GenPat p)
        Nothing  -> throwError $ UnknownTypeVar x
    (RecTy x r, _) -> do
      env <- ask
      checkTypePat cod dat (substRecTy (typeCxt env) x t r) p
    _ ->
      throwError $ TypePatternMismatch t (GenPat p)

checkTypeNewPat :: (MonadType x i m, Ord x, Ord i)
                => Type x i
                -> UnelabNewPat x i
                -> m (ElabNewPat x i)
checkTypeNewPat = checkTypePat checkFunTrm checkValTrm
  where checkFunTrm a u = checkTypeTrm (CBN ::: a) u
        checkValTrm a u = checkTypeTrm (CBV ::: a) u

checkTypeVal :: (MonadType x i m, Ord x, Ord i)
             => Type x i
             -> Val x i (UnelabPole x i) x x
             -> m (Val x i (ElabPole x i) x x)
checkTypeVal t (Struc v) = Struc <$> checkTypePat checkTypeCls checkAtom t v
  where checkAtom t x = checkTypeVar (CBV ::: t) x

checkTypeCls :: (MonadType x i m, Ord x, Ord i)
             => Type x i
             -> Cls x i (UnelabPole x i) x x
             -> m (Cls x i (ElabPole x i) x x)
checkTypeCls t (Free x)  = Free <$> checkTypeVar (CBN ::: t) x
checkTypeCls t (u :/: e) = do
  (e', env) <- elaborateEnv e
  u' <- local (env <>) $ checkTypeTrm (CBN ::: t) u
  return $ u' :/: e'

elaborateEnv :: (MonadType x i m, Ord x, Ord i)
             => Env x i (UnelabPole x i) x x
             -> m (Env x i (ElabPole x i) x x, TyInEnv x i)
elaborateEnv env = do
  env' <- traverse elaborateBound env
  let binds = getPoleBound <$> env'
  return (env', TyIn mempty binds)

elaborateBound :: (MonadType x i m, Ord x, Ord i)
               => Bound x i (UnelabPole x i) x x
               -> m (Bound x i (ElabPole x i) x x)
elaborateBound (LetFun (Check o) u) = do
  o'@(_ ::: t) <- normalizePole o
  u' <- checkTypeCls t u
  return $ LetFun o' u'
elaborateBound (LetVal (Check o) v) = do
  o'@(_ ::: t) <- normalizePole o
  v' <- checkTypeVal t v
  return $ LetVal o' v'
elaborateBound b = throwError $ UnannotatedBinding b

checkTypeRsp :: (MonadType x i m, Ord x, Ord i)
             => Type x i
             -> Rsp x i (UnelabPole x i)
             -> m (Rsp x i (ElabPole x i))
checkTypeRsp a (q :=> c) = (q :=>) <$> assignCoPatType a q (elaborateCmd c)

checkTypeRsps :: (MonadType x i m, Ord x, Ord i)
              => Type x i
              -> [Rsp x i (UnelabPole x i)]
              -> m [Rsp x i (ElabPole x i)]
checkTypeRsps o = traverse (checkTypeRsp o)

checkTypePatBind :: (Ord x, Ord i,
                     MonadReader (TyInEnv x i) m,
                     MonadError (TypeError x i) m)
                 => Type x i -> Pat i x x -> m (TyInEnv x i)
checkTypePatBind t p = do
  let bindVar s a x = do
        tell $ M.singleton x (s ::: a)
  (_, env) <- runWriterT $ checkTypePat (bindVar CBN) (bindVar CBV) t p
  return $ TyIn mempty env

checkTypeCoPatBind :: (Ord x, Ord i,
                       MonadReader (TyInEnv x i) m,
                       MonadError (TypeError x i) m)
                   => Type x i -> CoPat i x x -> m (TyInEnv x i)
checkTypeCoPatBind t (Nothing :.: p) = do
  checkTypePatBind t p
checkTypeCoPatBind t (Just x  :.: p) = do
  env <- checkTypePatBind t p
  return $ env{fromCxt = M.insert x (CBN ::: t) $ fromCxt env}


weaken :: (Ord x, MonadReader (TyInEnv x i) m)
       => x -> m a -> m a
weaken x = local (\env -> env{fromCxt = M.delete x $ fromCxt env})

assignType :: (Ord x, Ord i,
               MonadReader (TyInEnv x i) m,
               MonadError (TypeError x i) m)
           => x -> (ElabPole x i) -> m a -> m a
assignType x o m =
  local (\env -> env{fromCxt = M.insert x o $ fromCxt env}) m

assignPatType :: (Ord x, Ord i,
                 MonadReader (TyInEnv x i) m,
                 MonadError (TypeError x i) m)
              => Type x i -> Pat i x x -> m a -> m a
assignPatType t p m = do
  bind <- checkTypePatBind t p
  local (bind <>) m

assignCoPatType :: (Ord x, Ord i,
                    MonadReader (TyInEnv x i) m,
                    MonadError (TypeError x i) m)
                => Type x i -> CoPat i x x -> m a -> m a
assignCoPatType t q m = do
  bind <- checkTypeCoPatBind t q
  local (bind <>) m

expectPolarity :: MonadError (TypeError x i) m
               => Strat -> Strat -> Trm x i (UnelabPole x i) -> m ()
expectPolarity expected actual term
  | expected == actual = return ()
  | otherwise          = throwError $ MispolarTerm expected term actual

extractAnnotation :: UnelabPole x i -> Maybe (TyGoal x i)
extractAnnotation (Check p) = Just p
extractAnnotation _         = Nothing


normalizePole :: (Ord x, Ord i,
                  MonadReader (TyInEnv x i) m,
                  MonadError (TypeError x i) m)
              => TyGoal x i -> m (ElabPole x i)
normalizePole (s ::! TypeIs a) = return (s ::: a)
normalizePole (s ::! TypeOf x) = do
  env <- fromCxt <$> ask
  case M.lookup x env of
    Just (_ ::: t) -> return (s ::: t)
    Nothing        -> throwError $ UntypedVariable x


-- Unfold a recursive type one level by substitution.
--
-- Invariant: All types can only have `External` free type variables in them,
-- which must be found in the `TyInCxt` (specifically, the `typeCxt` field).
-- All occurrence of `Internal` variables must be locally bound within the type
-- (e.g., by a `rec \x = ...`).
--
-- Therefore, the only counter-example to naive substitution is when a local
-- binding of a type variable (from the external namespace) shadows something
-- visible in the global type context (`typeCxt`).  The type that is inserted
-- underneath that binding might have free references to that variable in the
-- global context that would get captured by the local binding.  To avoid the
-- capture, we can perform one step of freshening by moving the locally bound
-- type variable from the external namespace into the internal one, and update
-- all references to it simultaneously during substitution.
substRecTy :: (Ord x) => M.Map x a
           -> TyVar x -> Type x i
           -> Type x i -> Type x i
substRecTy cxt x r t0 = substTys cxt (M.singleton x r) t0

substTys :: (Ord x) => M.Map x a -> M.Map (TyVar x) (Type x i)
         -> Type x i -> Type x i
substTys cxt sub t0 = case t0 of
  VarTy x
    | Just t' <- M.lookup x sub
                -> t'
    | otherwise -> t0
  UnitTy -> UnitTy
  s `PairTy` t  -> substTys cxt sub s `PairTy` substTys cxt sub t
  TagTy its     -> TagTy (substTys cxt sub <$> its)
  ObjTy t       -> ObjTy (substTys cxt sub t)
  RecTy (External x) u
    | M.member x cxt
                -> RecTy (Internal x) (substTys cxt sub' u)
    where sub' = M.insert (External x) (VarTy $ Internal x) sub
  RecTy x u     -> RecTy x (substTys cxt sub u)

openUnionTy :: (Ord x, Ord i)
            => M.Map (TyVar x) (TyVar x)
            -> Type x i -> Type x i -> Maybe (Type x i)
openUnionTy eq s t = case (s, t) of
  (VarTy x, VarTy y) -> do
    z <- M.lookup x eq
    if y == z
      then Just (VarTy z)
      else Nothing
  (RecTy x s', RecTy y t') ->
     RecTy y <$> openUnionTy (M.insert x y eq) s' t'
  (ObjTy s', ObjTy t') ->
    ObjTy <$> openIntersectTy eq s' t'
  (UnitTy, UnitTy) ->
    Just UnitTy
  (s1 `PairTy` s2, t1 `PairTy` t2) ->
    PairTy <$> openUnionTy eq s1 t1 <*> openUnionTy eq s2 t2
  (TagTy xss, TagTy yts) ->
    TagTy <$> sequence (M.union right left)
    where left  = fmap (Just . renameTypeVars eq) xss
          right = M.mapWithKey mergeWithLeft yts
          mergeWithLeft x s' = case M.lookup x xss of
            Just t' -> openUnionTy eq s' t'
            Nothing -> Just s'
--  (SameTypeAs x, SameTypeAs y)
--    | x == y -> Just (SameTypeAs y)
  (_, _) -> Nothing

openIntersectTy :: (Ord x, Ord i)
                => M.Map (TyVar x) (TyVar x)
                -> Type x i -> Type x i -> Maybe (Type x i)
openIntersectTy eq s t = case (s, t) of
  (VarTy x, VarTy y) -> do
    z <- M.lookup x eq
    if y == z
      then Just (VarTy z)
      else Nothing
  (RecTy x s', RecTy y t') ->
     RecTy y <$> openUnionTy (M.insert x y eq) s' t'
  (ObjTy s', ObjTy t') ->
    ObjTy <$> openUnionTy eq s' t'
  (UnitTy, UnitTy) ->
    Just UnitTy
  (s1 `PairTy` s2, t1 `PairTy` t2) ->
    PairTy <$> openIntersectTy eq s1 t1 <*> openIntersectTy eq s2 t2
  (TagTy xss, TagTy yts) ->
    TagTy <$> sequence (M.intersectionWith common (Just <$> xss) (Just <$> yts))
    where common (Just l) (Just r) = openIntersectTy eq l r
          common _        _        = Nothing
--  (SameTypeAs x, SameTypeAs y)
--    | x == y -> Just (SameTypeAs y)
  (_, _) -> Nothing

partialUnionTy :: (Ord x, Ord i) => Type x i -> Type x i -> Maybe (Type x i)
partialUnionTy s t = openUnionTy (freeTypeVars s) s t
