{-# LANGUAGE OverloadedStrings #-}
module Coo.Source.Parse where

import Coo.Source.Syntax
import Coo.Grammar.Fixity
import Coo.Grammar.Lexer
-- import Coo.Grammar.Test

import qualified Data.Text as Txt
import Data.Foldable

-- import Text.Megaparsec
-- import Text.Megaparsec.Char


-- Source-specific lexing

type Keyword = String
type Symbol  = String

keywordList :: [Keyword]
keywordList = ["co", "val", "fun", "data", "type",
               "let", "in", "where",
               "do", "go", "as", "to", "fn",
               "match", "with", "case", "of",
               "if", "then", "else",
               "cbv", "cbn"]

keyword :: Parser Keyword
keyword = keywordFrom keywordList

co_, val_, fun_, data_, type_ :: Parser Keyword
let_, in_, where_             :: Parser Keyword
do_, go_, as_, to_, fn_       :: Parser Keyword
match_, with_, case_, of_     :: Parser Keyword
if_, then_, else_             :: Parser Keyword
cbv_, cbn_                    :: Parser Keyword

co_    = kw "co"
val_   = kw "val"
fun_   = kw "fun"
data_  = kw "data"
type_  = kw "type"
let_   = kw "let"
in_    = kw "in"
where_ = kw "where"
do_    = kw "do"
go_    = kw "go"
as_    = kw "as"
to_    = kw "to"
fn_    = kw "fn"
match_ = kw "match"
with_  = kw "with"
case_  = kw "case"
of_    = kw "of"
if_    = kw "if"
then_  = kw "then"
else_  = kw "else"
cbv_   = kw "cbv"
cbn_   = kw "cbn"

keysymbolList :: [Symbol]
keysymbolList = ["=", "=>", "<=", "|",
                 ".", "..", "...",
                 ",", ";", "!", "?"]

keysymbol :: Parser Symbol
keysymbol = keysymbolFrom keysymbolList

dot, dotdot, elipses :: Parser Symbol
dot     = ks "."
dotdot  = ks ".."
elipses = ks "..."

alt :: Parser Symbol
alt = ks "|"

equal, takes, gives :: Parser Symbol
equal = ks "="
takes = ks "<="
gives = ks "=>"

exclaim, question :: Parser Symbol
exclaim  = ks "!"
question = ks "?"

variable :: Parser Variable
variable = Txt.pack <$> boundAvoid keywordList <?> "variable"

unbound :: Parser Parameter
unbound = Unbound . Txt.pack <$> unboundName <?> "ignored parameter"

bound :: Parser Parameter
bound = Bound <$> variable <?> "bound parameter"

parameter :: Parser Parameter
parameter = unbound <|> bound <?> "parameter"

tag :: Parser TagName
tag = Txt.pack <$> freeName <?> "tag name"

literal :: Parser Literal
literal =  Flt <$> float
       <|> Int <$> decimal
       <|> Str <$> Txt.pack <$> inlineQuote
       <|> Tag <$> tag
       <?> "literal"

-- Parsing named definitions

defVal :: Parser def -> Parser (Pattern, Term)
defVal def =  val_ *> ((,) <$> (pat <* (takes <|> equal)) <*> nonemptyTerm)
          <|> try ((,) <$> (pat <* def) <*> nonemptyTerm)

defFun :: Parser def -> Parser Reaction
defFun def =  fun_ *> reactEq (gives <|> equal)
          <|> try (reactEq1 def)

-- Parsing Statements / Commands

statement :: Parser Statement
statement =  Go <$> (go_ *> term)
                <*> optional (as_ *> annote)
                <*> optional (to_ *> term)
         <|> Case <$> ((match_ <|> case_) *> term)
                  <*> reactSwitch empty
         <|> If <$> (if_ *> reactIf execsCmd)
         <|> uncurry SetMatch <$> defVal (takes <|> equal)
                              <*> optional (if_ *> reactCaveat)
                              <*> optional (else_ *> reactWhole)
         <|> LocalFun <$> defFun gives
         <|> Run <$> nonemptyTerm
         <?> "statement"

basicCommand :: Parser Command
basicCommand =  braces command
            <|> (:[]) <$> statement
            <?> "basic command"

command :: Parser Command
command =  concat <$> (basicCommand `sepEndBy` semicolon)
       <?> "command"

statementInit :: Parser String
statementInit =  go_ <|> match_ <|> case_ <|> if_ <|> val_ <|> fun_

-- Parsing (Co)Terms

basicTerm :: Parser Term
basicTerm =  Var . Bound <$> variable
         <|> construction
         <|> Do <$> (do_ *> reactWhole)
         <|> Fn <$> (fn_ *> reactStack)
         <|> Obj <$> braces term
         <|> parens term
         <?> "basic term"

construction :: Parser Term
construction =  Make <$> literal <*> constrArg
            -- <|> Make <$> pure (Tag mempty) <*> brackets term
            <?> "construction"

constrArg :: Parser Term
constrArg =  brackets term
         <|> pure Nil
         <?> "constructor argument"

nonemptyTerm :: Parser Term
nonemptyTerm =  parseOpTable coreOpTable basicTerm
            <|> statementInit *> fail "expecting a term, not a statement"
            <?> "nonempty term"

term :: Parser Term
term =  nonemptyTerm
    <|> pure Nil
    <?> "term"

basicCoterm :: Parser CoTerm
basicCoterm = basicTerm <?> "basic coterm"

coterm :: Parser CoTerm
coterm = parseOpTable coreOpTable basicCoterm <?> "coterm"

coreOpTable :: OperationTable Parser Term
coreOpTable = [ leftward  $ postfixOp dotOp <> infixLOp appOp,
                rightward $ infixROp (adhocBinOp "^"),
                leftward
                  $  infixLOp (adhocBinOp "*")
                  <> infixLOp (adhocBinOp "/")
                  <> infixLOp (adhocBinOp "%"),
                leftward  $ infixLOp (adhocBinOp "+") <> infixLOp (adhocBinOp "-"),
                leftward
                  $  infixLOp (adhocBinOp "<")
                  <> infixLOp (adhocBinOp ">")
                  <> infixLOp (adhocBinOp "=<")
                  <> infixLOp (adhocBinOp ">="),
                leftward  $ infixLOp (adhocBinOp "==") <> infixLOp (adhocBinOp "/="),
                rightward $ prefixOp evalOp <> infixROp callOp,
                rightward $ infixROp pairOp ]

dotOp :: Parser (Term -> Term)
dotOp = try dot >> flip Dot <$> literal

appOp :: Parser (Term -> Term -> Term)
appOp = pure App

pairOp :: Parser (Term -> Term -> Term)
pairOp = comma >> pure Pair

evalOp :: Parser (Term -> Term)
evalOp = emark >> pure Call

callOp :: Parser (Term -> Term -> Term)
callOp = emark >> pure (\f a -> f `App` Call a)

adhocBinOp :: String -> Parser (Term -> Term -> Term)
adhocBinOp name = do
  ks name
  return $ \x y -> (Var (Bound $ Txt.pack name) `App` x) `App` y

-- Parsing (Co)Patterns

basicPat :: Parser Pattern
basicPat =  Any <$> parameter
        <|> constPat
        <|> IsObj <$> braces parameter
        <|> parens pat
        <?> "basic pattern"

constPat :: Parser Pattern
constPat =  Made <$> literal <*> (brackets pat <|> pure IsNil)
        <|> Made <$> pure (Tag mempty) <*> brackets pat
        <?> "constructor pattern"

nonemptyPat :: Parser Pattern
nonemptyPat =  parseOpTable corePatOpTable basicPat
--           <|> Many Nothing <$> (dotdot *> parameter)
           <?> "nonemtpy pattern"

pat :: Parser Pattern
pat = nonemptyPat <|> pure IsNil <?> "pattern"

argPat :: Parser Pattern
argPat =  basicPat
      <|> rejectSplatArg
      <?> "pattern argument"

rejectSplatArg :: Parser Pattern
rejectSplatArg = do
  _ <- dotdot
  x <- variable
  let oops = "\".." ++ Txt.unpack x ++ "\" is not a pattern argument, "
  let hint = "did you mean \"(.." ++ Txt.unpack x ++ ")\"?"
  fail $ oops ++ hint

dotCoPat :: Parser Literal
dotCoPat =  (dot *> literal)
        <?> "dot copattern"

basicCopat :: Parser CoPattern
basicCopat =  SelfIs <$> parameter
          <|> parens copat
          <?> "basic copattern"

copat :: Parser CoPattern
copat = parseOpTable coreCoPatOpTable basicCopat <?> "copattern"

corePatOpTable :: OperationTable Parser Pattern
corePatOpTable = [ --leftward $ postfixOp splatPatOp,
                   rightward $ infixROp pairPatOp ]

coreCoPatOpTable :: OperationTable Parser CoPattern
coreCoPatOpTable = [ leftward  $ postfixOp dotCoPatOp <> postfixOp appCoPatOp ]

pairPatOp :: Parser (Pattern -> Pattern -> Pattern)
pairPatOp = comma >> pure IsPair

{-
splatPatOp :: Parser (Pattern -> Pattern)
splatPatOp = matchOnMany <$> (dotdot *> parameter)
  where matchOnMany var subPat = Many (Just subPat) var
-}

appCoPatOp :: Parser (CoPattern -> CoPattern)
appCoPatOp = flip CoApp <$> argPat

dotCoPatOp :: Parser (CoPattern -> CoPattern)
dotCoPatOp = flip CoDot <$> dotCoPat



-- Parsing Reactions

reactSwitch :: Parser Reaction -> Parser Reaction
reactSwitch rhs =  if_ *> reactIf rhs
               <|> (to_ <|> with_) *> reactWhole
               <|> (of_ <|> in_) *> reactStack
               <|> (as_ <|> where_) *> reactEq (gives <|> equal)
               <|> fun_ *> reactLetFun rhs
               <|> else_ *> reactElse rhs
               <|> rhs
               <?> "explicit reaction mode"

reactAlts :: Parser Reaction -> Parser Reaction
reactAlts mode =  reactAltsGroup mode
              <|> reactAltsBlock mode
              <?> "reaction alternatives"

reactAltsGroup :: Parser Reaction -> Parser Reaction
reactAltsGroup mode = braces $ alt *> (fold <$> mode `sepBy` alt)

reactAltsBlock :: Parser Reaction -> Parser Reaction
reactAltsBlock mode = alt *> (fold <$> mode `sepBy` alt)

reactNest :: Parser Reaction -> Parser Reaction -> Parser Reaction
reactNest mode rhs =  reactSwitch rhs
                  <|> reactAlts mode
                  <?> "nested reaction"

reactStack, reactStack1 :: Parser Reaction
reactStack1 =  Pop <$> try argPat <*> reactStack
           <|> Proj <$> dotCoPat <*> reactStack
           <?> "functional reaction"

reactStack =  reactStack1
          <|> reactNest reactStack evalsTerm

reactWhole, reactWhole1 :: Parser Reaction
reactWhole1 =  Rest <$> try nonemptyPat <*> reactSwitch execsCmd
           <?> "pattern reaction"

reactWhole =  reactWhole1
          <|> reactNest reactWhole execsCmd

reactIf, reactIf1 :: Parser Reaction -> Parser Reaction
reactIf1 rhs =  Guard <$> optional guardPattern <*> try nonemptyTerm
                      <*> reactNest (reactIf rhs) rhs
            <?> "conditional reaction"
  where guardPattern =  val_ *> pat <* (takes <|> equal)
                    <|> try (pat <* takes)
                    <?> "guard pattern"

reactIf rhs =  reactIf1 rhs
           <|> reactNest (reactIf rhs) rhs

reactLetFun :: Parser Reaction -> Parser Reaction
reactLetFun rhs =  LetFun <$> defFun gives <*> reactSwitch rhs

reactElse :: Parser Reaction -> Parser Reaction
reactElse rhs = Else <$> parameter <*> reactSwitch rhs

reactCaveat :: Parser Reaction
reactCaveat = reactIf (pure Cede)

reactEq, reactEq1 :: Parser def -> Parser Reaction
reactEq1 def =  Rec <$> (go_ *> copat)
                    <*> (Rest <$> (to_ *> pat)
                              <*> reactNest (reactEq def) (rhsCmd def))
            <|> Rec <$> copat <*> reactNest (reactEq def) (rhsTerm def)
            <?> "copattern reaction"

reactEq def =  reactEq1 def
           <|> reactNest (reactEq def) empty

rhsTerm :: Parser a -> Parser Reaction
rhsTerm def = Eval <$> (def *> nonemptyTerm)

rhsCmd :: Parser a -> Parser Reaction
rhsCmd def = Exec <$> (def *> basicCommand)

evalsTerm, equalsTerm, execsCmd, equalsCmd :: Parser Reaction
evalsTerm  = rhsTerm gives
equalsTerm = rhsTerm equal
execsCmd   = rhsCmd  gives
equalsCmd  = rhsCmd  equal

-- Parsing module declarations

declare :: Parser Declaration
declare = uncurry Field <$> defVal takes
       <|> Function <$> defFun (gives <|> equal)

bindings :: Parser Bindings
bindings = declare `endBy` semicolon

modul :: Parser Module
modul = Package <$> bindings <*> term

-- Parsing Types and Annotations

annote :: Parser Annotation
annote =  OfPolarity <$> strategy
      <|> OfType <$> typ
      <?> "typing annotation"

strategy :: Parser Strat
strategy =  (const CBV <$> cbv_)
        <|> (const CBN <$> cbn_)

typ :: Parser Type
typ = undefined

{-
basicType :: Parser Type
basicType =  TyLit <$> complexLiteral
         <|> TyVar <$> variable
         <|> TyBox <$> brackets typ
         <|> TyObj <$> braces typ
         <|> parens typ
         <?> "basic type"

nonemptyType :: Parser Type
nonemptyType =  parseOpTable coreTyOpTable basicType
            <?> "nonempty type"

typ :: Parser Term
typ =  nonemptyType
   <|> pure TyNil
   <?> "type"

coreTyOpTable :: OperationTable Parser Type
coreTyOpTable = [ leftward $ postfixOp splatTyOp,
                  leftward  $ postfixOp dotOp <> infixLOp appTyOp,
                  rightward $ infixROp pairTyOp,
                  rightward $ infixROp unionTyOp ]

dotOp :: Parser (Term -> Term)
dotOp = dot >> pure Dot

appOp :: Parser (Term -> Term -> Term)
appOp = pure App

splatOp :: Parser (Term -> Term)
splatOp = dotdot >> pure Splat

pairOp :: Parser (Term -> Term -> Term)
pairOp = comma >> pure Pair


fun fst (x, y) = return x;
fun snd (x, y) = return y;

fun (count n).Head = return n
  | (count n).Tail = count(n+1);

fun nats = count 0;

fun zips xs ys .Head = return (xs.Head, ys.Head)
  | zips xs ys .Tail = zips (xs.Head) (ys.Head);

fun maps {f} as
  | (mapf xs).Head = f (xs.Head)
  | (mapf xs).Tail = mapf (xs.Tail);

fun go infiniteFilter     p xs to start
  = go infiniteFilterSwap p xs to start, start;

fun go infiniteFilterSwap {p} as
  | loop xs _ .Head = xs.Head
  | go loop xs other .Tail to this
    if | p(xs.Head) == p(xs.Tail.Head) = go loop (xs.Tail) other to this
       |                               = go loop (xs.Tail) this  to other;

fun infinitePigeons bits
  = maps {fst} (infiniteFilter {snd} (zips {nats} bits));
-}
