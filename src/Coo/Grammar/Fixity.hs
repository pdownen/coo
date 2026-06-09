{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
module Coo.Grammar.Fixity where

import Control.Applicative

optionalOp :: Alternative f => f (a -> a) -> f (a -> a)
optionalOp op = op <|> pure id

{-
initial :: Applicative f => f (a -> b) -> f a -> f b
initial op term = op <*> term

terminal :: Applicative f => f a -> f (a -> b) -> f b
terminal term op = term <**> op
-}

leftOf :: Applicative f => f (a -> b -> c) -> f b -> f (a -> c)
leftOf op right = flip <$> op <*> right

rightOf :: Applicative f => f (a -> b -> c) -> f a -> f (b -> c)
rightOf op left = left <**> op

leftAndRight :: Applicative f => f (a -> b) -> f (b -> c) -> f a -> f c
leftAndRight left right term = (left <*> term) <**> right

rightAndLeft :: Applicative f => f (b -> c) -> f (a -> b) -> f a -> f c
rightAndLeft left right term = left <*> (term <**> right)

dynamicGroup :: Monad m => m (m (a -> b)) -> m a -> m b
dynamicGroup begin term = do
  end <- begin
  term <**> end


unaryR, unaryR1 :: Alternative f => f (b -> b) -> f (b -> b)
unaryR  op = optionalOp $ unaryR1 op
unaryR1 op = (\f fs -> f . fs) <$> op <*> unaryR op

prefix, prefix1 :: Alternative f => f (a -> a) -> f a -> f a
prefix  op term = unaryR  op <*> term
prefix1 op term = unaryR1 op <*> term

unaryL, unaryL1 :: Alternative f => f (a -> a) -> f (a -> a)
unaryL  op = optionalOp $ unaryL1 op
unaryL1 op = (\f fs -> fs . f) <$> op <*> unaryL op

postfix, postfix1 :: Alternative f => f a -> f (a -> a) -> f a
postfix  term op = term <**> unaryL  op
postfix1 term op = term <**> unaryL1 op


infix1 :: Applicative f => f (a -> b -> c) -> f a -> f b -> f c
infix1 op left right = left <**> op <*> right

infixN :: Alternative f => f (a -> b -> a) -> f a ->  f b -> f a
infixN op left right = left <**> optionalOp (op `leftOf` right)

infixL :: Alternative f => f (a -> a -> a) -> f a -> f a
infixL op term = infixL' op term term

infixL' :: Alternative f => f (a -> b -> a) -> f a -> f b -> f a
infixL' op left right = left <**> unaryL (op `leftOf` right) 

infixR :: Alternative f => f (a -> a -> a) -> f a -> f a
infixR op term = term <**> optionalOp (op `leftOf` infixR op term)

infixR' :: Alternative f => f (a -> b -> b) -> f a -> f b -> f b
infixR' op left right = left <**> op <*> infixR' op left right <|> right


postInfixL :: Alternative f => f (a -> a) -> f (a -> a -> a) -> f a -> f a
postInfixL post bin term = postInfixL' post bin term term

postInfixL' :: Alternative f => f (a -> a) -> f (a -> b -> a) -> f a -> f b -> f a
postInfixL' post bin left right = left <**> unaryL (post <|> bin `leftOf` right)

preInfixR :: Alternative f => f (a -> a) -> f (a -> a -> a) -> f a -> f a
preInfixR pre bin term =  pre  <*>  preInfixR pre bin term
                      <|> term <**> optionalOp (bin `leftOf` preInfixR pre bin term)

preInfixR' :: Alternative f => f (b -> b) -> f (a -> b -> b) -> f a -> f b -> f b
preInfixR' pre bin left right =  pre           <*> preInfixR' pre bin left right
                             <|> left <**> bin <*> preInfixR' pre bin left right
                             <|> right


type OperationLevel f a = f a -> f a
type OperationTable f a = [OperationLevel f a]

parseOpLevel :: Alternative f => OperationLevel f a -> f a -> f a
parseOpLevel op term = op term

parseOpTable :: Alternative f => OperationTable f a -> f a -> f a
parseOpTable table term = foldl (flip parseOpLevel) term table


data LeftwardOp  f a = LOp (f (a -> a -> a)) (f (a -> a))
data RightwardOp f a = ROp (f (a -> a)) (f (a -> a -> a))
data NonAssocOp  f a = NOp (f (a -> a -> a))
data AmbiguousOp f a = AmbOp { preP    :: f (a -> a),
                               rightP  :: f (a -> a -> a),
                               midP    :: f (a -> a -> a),
                               leftP   :: f (a -> a -> a),
                               postP   :: f (a -> a) }


prefixOp :: Alternative f => f (a -> a) -> RightwardOp f a
prefixOp  op = ROp op empty

postfixOp :: Alternative f => f (a -> a) -> LeftwardOp f a
postfixOp op = LOp  empty op

infixROp :: Alternative f => f (a -> a -> a) -> RightwardOp f a
infixROp op = ROp empty op

infixLOp :: Alternative f => f (a -> a -> a) -> LeftwardOp f a
infixLOp op = LOp  op empty

infixNOp :: f (a -> a -> a) -> NonAssocOp f a
infixNOp op = NOp  op

instance Alternative f => Semigroup (LeftwardOp f a) where
  LOp bin1 post1 <> LOp bin2 post2 = LOp (bin1 <|> bin2) (post1 <|> post2)

instance Alternative f => Monoid (LeftwardOp f a) where
  mempty = LOp empty empty

instance Alternative f => Semigroup (RightwardOp f a) where
  ROp pre1 bin1 <> ROp pre2 bin2 = ROp (pre1 <|> pre2) (bin1 <|> bin2)

instance Alternative f => Monoid (RightwardOp f a) where
  mempty = ROp empty empty

instance Alternative f => Semigroup (NonAssocOp f a) where
  NOp bin1 <> NOp bin2 = NOp (bin1 <|> bin2)

instance Alternative f => Monoid (NonAssocOp f a) where
  mempty = NOp empty

instance (Alternative f) => Semigroup (AmbiguousOp f a) where
  AmbOp pre1 r1 m1 l1 post1 <> AmbOp pre2 r2 m2 l2 post2
    = AmbOp (pre1 <|> pre2) (r1 <|> r2) (m1 <|> m2) (l1 <|> l2) (post1 <|> post2)

instance (Alternative f) => Monoid (AmbiguousOp f a) where
  mempty = AmbOp empty empty empty empty empty


emptyAmbiguousOp :: Alternative f => AmbiguousOp f a
emptyAmbiguousOp
  = AmbOp{preP=empty, rightP=empty, midP=empty, leftP=empty, postP=empty}

ambL :: Alternative f => LeftwardOp f a -> AmbiguousOp f a
ambL (LOp bin post) = emptyAmbiguousOp{leftP=bin, postP=post}

ambR :: Alternative f => RightwardOp f a -> AmbiguousOp f a
ambR (ROp pre bin)  = emptyAmbiguousOp{rightP=bin, preP=pre}

ambN :: Alternative f => NonAssocOp f a -> AmbiguousOp f a
ambN (NOp bin)      = emptyAmbiguousOp{midP=bin}


leftward :: Alternative f => LeftwardOp f a -> OperationLevel f a
leftward (LOp bin post) = postInfixL post bin

rightward :: Alternative f => RightwardOp f a -> OperationLevel f a
rightward (ROp pre bin)  = preInfixR pre bin

nonassoc :: Alternative f => NonAssocOp f a -> OperationLevel f a
nonassoc (NOp bin) term = infixN bin term term

nonR, nonL, nonN :: Alternative f => AmbiguousOp f a -> AmbiguousOp f a
nonR ops = ops{preP = empty, rightP = empty}
nonL ops = ops{postP = empty, leftP = empty}
nonN ops = ops{midP = empty}

autoPrec :: Alternative f => AmbiguousOp f b -> f b -> f b
autoPrec ops@AmbOp{..} term
   =  preP <*>  preInfixR preP rightP (autoPrec (nonR ops) term)
  <|> term <**> (   rightP `leftOf` preInfixR preP rightP (autoPrec (nonR ops) term)
                <|> unaryL1 (postP <|> leftP `leftOf` autoPrec (nonL ops) term)
                <|> midP `leftOf` autoPrec (nonN ops) term
                <|> pure id
                )

autoTable :: Alternative f => [AmbiguousOp f a] -> OperationTable f a
autoTable = map autoPrec

ambiguous :: (Alternative f, MonadFail f) => String -> AmbiguousOp f a -> OperationLevel f a
ambiguous opLevel AmbOp{..} term
   =  preP <*> preInfixR preP onlyRightP term
  <|> term <**> ( unaryL1 (postP <|> onlyLeftP `leftOf` noPrefix "left")
                <|> rightP `leftOf` preInfixR preP onlyRightP term
                <|> midP `leftOf` noPrefix "non"
                <|> pure id
                )
  where ambError assoc = "Ambiguous fixity level " ++ opLevel ++
                         ": expected a " ++ assoc ++ "-associative operator"
        ban op assoc = op >> fail (ambError assoc)
        onlyRightP = rightP <|> ban (leftP <|> midP) "right" <|> ban postP "right"
        onlyLeftP  = leftP <|> ban (rightP <|> midP) "left"
        noPrefix assoc = term <|> ban preP assoc

ambiguousTable :: (Alternative f, MonadFail f)
               => [(String, AmbiguousOp f a)] -> OperationTable f a
ambiguousTable = map (uncurry ambiguous)
