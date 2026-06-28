module Coo.Grammar.Lexer
  (module Coo.Grammar.Lexer,
   module Text.Megaparsec,
   module Text.Megaparsec.Char)
where

import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

initial, final, whole, perfect :: Parser a -> Parser a
initial p = skipComments *> p
final p   = p <* eof
whole p   = final (initial p)
perfect p = skipSpaceOnly *> p <* eof

anything :: Parser String
anything = takeRest

lineComment, blockComment :: Parser ()
lineComment = L.skipLineComment "#"
blockComment = L.skipBlockCommentNested "#[" "]#"

skipComments :: Parser ()
skipComments = L.space space1 lineComment blockComment

skipSpaceOnly :: Parser ()
skipSpaceOnly = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme skipComments

exact :: String -> Parser String
exact = L.symbol skipSpaceOnly

str :: String -> Parser String
str = L.symbol skipComments

parens, braces, brackets, angles :: Parser a -> Parser a
parens   = between (str "(") (str ")")
braces   = between (str "{") (str "}")
brackets = between (str "[") (str "]")
angles   = between (str "<") (str ">")

comma, colon, semicolon, period, qmark, emark :: Parser Char
comma     = lexeme $ char ','
colon     = lexeme $ char ':'
semicolon = lexeme $ char ';'
period    = lexeme $ char '.'
qmark     = lexeme $ char '?'
emark     = lexeme $ char '!'

underscore :: Parser Char
underscore = lexeme $ char '_'

decimal :: Num a => Parser a
decimal = lexeme $ L.decimal

integer :: Num a => Parser a
integer = lexeme $ try $ L.signed (pure ()) L.decimal

float :: RealFloat a => Parser a
float = lexeme $ try $ L.signed (pure ()) L.float

inlineQuote :: Parser String
inlineQuote = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

nameLetter :: Parser Char
nameLetter = alphaNumChar <|> oneOf ['_', '\'']

nameLetters :: Parser String
nameLetters = many nameLetter

extraOpSymbols :: [Char]
extraOpSymbols = ['.', ',', '!', '?', '_', '\'']

opSymbol :: Parser Char
opSymbol = symbolChar <|> oneOf extraOpSymbols

opSymbols :: Parser String
opSymbols = many symbolChar

boundFirstLetter :: Parser Char
boundFirstLetter = lowerChar

boundName :: Parser String
boundName = lexeme $ try $ (:) <$> boundFirstLetter <*> nameLetters

unboundFirstLetter :: Parser Char
unboundFirstLetter = char '_'

unboundName :: Parser String
unboundName = lexeme $ try $ (:) <$> unboundFirstLetter <*> nameLetters

freeFirstLetter :: Parser Char
freeFirstLetter = upperChar

freeName :: Parser String
freeName = lexeme $ try $ (:) <$> freeFirstLetter <*> nameLetters

opFirstSymbol :: Parser Char
opFirstSymbol = symbolChar

opName :: Parser String
opName = lexeme $ try $ (:) <$> opFirstSymbol <*> opSymbols

wholeName :: Parser a -> Parser a
wholeName name = name <* notFollowedBy nameLetter

kw :: String -> Parser String
kw word = lexeme $ try $ wholeName $ string word

keywordFrom :: [String] -> Parser String
keywordFrom kws = choice $ map kw kws

boundAvoid :: [String] -> Parser String
boundAvoid kws = try $ do x <- boundName
                          if x `elem` kws
                            then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                            else return x

wholeSymbol :: Parser a -> Parser a
wholeSymbol sym = sym <* notFollowedBy opSymbol

ks :: String -> Parser String
ks sym = lexeme $ try $ wholeSymbol $ string sym

keysymbolFrom :: [String] -> Parser String
keysymbolFrom ops = choice $ map ks ops

opAvoid :: [String] -> Parser String
opAvoid ops = try $ do x <- opName
                       if x `elem` ops
                         then fail $ "key symbol " ++ show x ++ " cannot be an operator"
                         else return x
