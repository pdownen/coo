{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
module Coo.Source.Simplify where

import Coo.Source.Syntax

toReactAlts :: Reaction -> [Reaction]
toReactAlts Cede          = []
toReactAlts (r1 `Alt` r2) = toReactAlts r1 ++ toReactAlts r2
toReactAlts r             = [r]

fromReactAlts :: [Reaction] -> Reaction
fromReactAlts [r] = r
fromReactAlts rs  = foldr Alt Cede rs

flattenReactAlts :: Reaction -> Reaction
flattenReactAlts = fromReactAlts . toReactAlts

distributeReactAlts :: Reaction -> [Reaction]
distributeReactAlts r = case r of
  p `Rest` r'   -> [ p `Rest` r'' | r'' <- distributeReactAlts r' ]
  p `Pop`  r'   -> [ p `Pop`  r'' | r'' <- distributeReactAlts r' ]
  i `Proj` r'   -> [ i `Proj` r'' | r'' <- distributeReactAlts r' ]
  q `Rec`  r'   -> [ q `Rec`  r'' | r'' <- distributeReactAlts r' ]
  x `Else` r'   -> [ x `Else` r'' | r'' <- distributeReactAlts r' ]
  Guard p t r'  -> [Guard p t $ distributeReact r']
  LetFun d f r' -> [LetFun d f $ distributeReact r']
  Cede          -> []
  r1 `Alt` r2   -> distributeReactAlts r1 ++ distributeReactAlts r2
  Exec c        -> [Exec c]
  Eval t        -> [Eval t]

distributeReact :: Reaction -> Reaction
distributeReact = fromReactAlts . distributeReactAlts

data ReactionContext = ReCxt { comatch   :: CoPattern,
                               remainder :: Maybe Pattern,
                               aliases   :: [(FunDeclare, Reaction)],
                               response  :: Reaction }
                     deriving (Show)

inEmptyReactCxt :: ReactionContext -> Maybe Reaction
inEmptyReactCxt (ReCxt (SelfIs (Unbound _)) Nothing [] r) = Just r
inEmptyReactCxt _                                         = Nothing

pattern EmptyReactCxt :: Reaction -> ReactionContext
pattern EmptyReactCxt r <- (inEmptyReactCxt -> Just r)
  where EmptyReactCxt r = ReCxt (SelfIs Blank) Nothing [] r

mergeInnerContext :: CoPattern -> ReactionContext -> ReactionContext
mergeInnerContext q cxt = case extractSelfBind (comatch cxt) of
  Just x  -> cxt{ comatch = q `appendCoPat` comatch cxt,
                  aliases = (emptyFunDecl, makeRecAlias x q) : aliases cxt }
  Nothing -> cxt{ comatch = q `appendCoPat` comatch cxt }

gatherReactCxt :: Reaction -> ReactionContext
gatherReactCxt r = case r of
  q `Rec`  r'
    -> mergeInnerContext q $ gatherReactCxt r'
  p `Pop`  r'
    -> mergeInnerContext (SelfIs Blank `CoApp` p) $ gatherReactCxt r'
  i `Proj` r'
    -> mergeInnerContext (SelfIs Blank `CoDot` i) $ gatherReactCxt r'
  p `Rest` r'
    -> ReCxt (SelfIs Blank) (Just p) [] r'
  LetFun d f r'
    -> let cxt = gatherReactCxt r'
       in cxt{aliases = (d, f) : aliases cxt}
  Eval (Shift (PS CBN You) t)
    -> ReCxt (SelfIs Blank) (Just $ IsObj $ Implicit Here) []
       (Exec [Go t (Just $ Annote (Check CBV) ToGo) (Just $ Var $ Implicit Here)])
  _ -> EmptyReactCxt r

compressReactCxt :: ReactionContext -> Reaction
compressReactCxt cxt
  = mergeRecRest $ recursivePart $ remainderPart $ bindRecAliases (aliases cxt) (response cxt)
  where recursivePart r = comatch cxt `ensureRec` r
        remainderPart r = case remainder cxt of
          Just p  -> p `Rest` r
          Nothing -> r

mergeRecRest :: Reaction -> Reaction
mergeRecRest (q `Rec` (p `Rest` r)) = case reassocToPat q p of
  (Nothing, p') -> p' `Rest` r
  (Just x, p') -> (SelfIs x `Rec` (p' `Rest` r))
mergeRecRest r = r

bindRecAliases :: [(FunDeclare, Reaction)] -> Reaction -> Reaction
bindRecAliases []          r = r
bindRecAliases ((d, a):as) r = LetFun d a $ bindRecAliases as r

makeRecAlias :: Parameter -> CoPattern -> Reaction
makeRecAlias x q = (SelfIs x' `Rec` Eval (copatToTerm q))
  where x' = case x of
          Unbound _ -> Implicit Self
          _         -> x

compressReactSteps :: Reaction -> Reaction
compressReactSteps (Guard p t r')
  = Guard p t $ compressReactSteps r'
compressReactSteps (r1 `Alt` r2)
  = compressReactSteps r1 `Alt` compressReactSteps r2
compressReactSteps r
  = case gatherReactCxt r of
      EmptyReactCxt _ -> r
      cxt -> compressReactCxt cxt{response = compressReactSteps (response cxt)}

removeBlankCoPat :: Reaction -> Reaction
removeBlankCoPat (SelfIs (Unbound _) `Rec` r) = r
removeBlankCoPat r                            = r

appendCoPat :: CoPattern -> CoPattern -> CoPattern
appendCoPat q (SelfIs _)     = q
appendCoPat q (q' `CoApp` p) = appendCoPat q q' `CoApp` p
appendCoPat q (q' `CoDot` i) = appendCoPat q q' `CoDot` i

ensureRec :: CoPattern -> Reaction -> Reaction
ensureRec q r
  | immediate r = q `Rec` r
  | otherwise   = ensureCoPatRec q `Rec` r
  where immediate r0 = case r0 of
          Eval _      -> True
          Exec _      -> True
          _ `Rest` r' -> immediate r'
          _ `Pop`  r' -> immediate r'
          _ `Proj` r' -> immediate r'
          _           -> False

ensureCoPatRec :: CoPattern -> CoPattern
ensureCoPatRec (SelfIs (Unbound _)) = SelfIs (Implicit Self)
ensureCoPatRec (SelfIs x)           = SelfIs x
ensureCoPatRec (q `CoApp` p)        = ensureCoPatRec q `CoApp` p
ensureCoPatRec (q `CoDot` i)        = ensureCoPatRec q `CoDot` i

pushNonRec :: Pattern -> CoPattern -> Maybe CoPattern
pushNonRec p q@(SelfIs (Unbound _)) = Just $ q `CoApp` p
pushNonRec p (q `CoApp` p')
  | Just q' <- pushNonRec p q       = Just $ q' `CoApp` p'
pushNonRec p (q `CoDot` i)
  | Just q' <- pushNonRec p q       = Just $ q' `CoDot` i
pushNonRec _ _                      = Nothing

sendNonRec :: Literal -> CoPattern -> Maybe CoPattern
sendNonRec i q@(SelfIs (Unbound _)) = Just $ q `CoDot` i
sendNonRec i (q `CoApp` p)
  | Just q' <- sendNonRec i q       = Just $ q' `CoApp` p
sendNonRec i (q `CoDot` j)
  | Just q' <- sendNonRec i q       = Just $ q' `CoDot` j
sendNonRec _ _                      = Nothing


simplifyReacts1 :: Reaction -> Reaction
simplifyReacts1 = compressReactSteps . distributeReact

simplifyReacts :: Reaction -> Reaction
simplifyReacts = simplifyReacts1 . simplifyInside
  where simplifyInside r0 = case r0 of
          Eval t       -> Eval $ simplifyReactsTrm t
          Exec c       -> Exec $ simplifyReactsCmd c
          p `Rest` r   -> p `Rest` simplifyInside r
          p `Pop`  r   -> p `Pop` simplifyInside r
          i `Proj` r   -> i `Proj` simplifyInside r
          q `Rec`  r   -> q `Rec` simplifyInside r
          Guard p t r  -> Guard p (simplifyReactsTrm t) (simplifyInside r)
          LetFun d f r -> LetFun d (simplifyReacts f) (simplifyInside r)
          Else x r     -> Else x (simplifyInside r)
          r1 `Alt` r2  -> simplifyInside r1 `Alt` simplifyInside r2
          Cede         -> Cede

simplifyReactsTrm :: Term -> Term
simplifyReactsTrm t0 = case t0 of
  Var x      -> Var x
  Do r       -> Do (simplifyReacts r)
  Fn r       -> Fn (simplifyReacts r)
  Nil        -> Nil
  Pair t u   -> Pair (simplifyReactsTrm t) (simplifyReactsTrm u)
  App  t u   -> App (simplifyReactsTrm t) (simplifyReactsTrm u)
  Call t     -> Call (simplifyReactsTrm t)
  Obj  t     -> Obj (simplifyReactsTrm t)
  Make i t   -> Make i (simplifyReactsTrm t)
  Dot  t i   -> Dot (simplifyReactsTrm t) i
  AsType t a -> AsType (simplifyReactsTrm t) a
  Shift p t  -> Shift p (simplifyReactsTrm t)
  

simplifyReactsCmd :: Command -> Command
simplifyReactsCmd = fmap simplifyReactsStm

simplifyReactsStm :: Statement -> Statement
simplifyReactsStm s = case s of
  Go u a t         -> Go (simplifyReactsTrm u) a (simplifyReactsTrm <$> t)
  Run t            -> Run (simplifyReactsTrm t)
  LocalFun d r     -> LocalFun d (simplifyReacts r)
  SetMatch p t c h ->
    SetMatch p (simplifyReactsTrm t) (simplifyReactsCaveat <$> c) (simplifyReacts <$> h)
  If r             -> If (simplifyReacts r)
  Case t r         -> Case (simplifyReactsTrm t) (simplifyReacts r)

simplifyReactsCaveat :: SetCaveat -> SetCaveat
simplifyReactsCaveat (p, t) = (p, simplifyReactsTrm t)
