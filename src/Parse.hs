module Parse (src) where

import Types

import Control.Monad.Combinators.NonEmpty
import Data.Char
import Relude hiding (many, some, pi)
import Relude.Extra
import Text.Megaparsec hiding (many, some)
import Text.Megaparsec.Char (space1)
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text

sc ∷ Parser ()
sc = L.space space1 empty empty

keyword, symbol ∷ Text → Parser ()
keyword kw = try $ word >>= guard . (== kw)
symbol = void . L.lexeme sc . chunk

word, ident ∷ Parser Text
word = L.lexeme sc $ takeWhile1P Nothing isAlphaNum
ident = try $ do
  i ← word
  guard (i `notElem` keywords) $> i
  where keywords = ["let", "in"]

parens ∷ Parser a → Parser a
parens = between (symbol "(") (symbol ")")

binder ∷ Parser Name
binder = "" <$ symbol "_" <|> ident

pi ∷ Parser Term
pi = do
  doms ← some (parens $ liftA2 (,) (some binder) (symbol ":" *> expr))
    <&> (>>= \(vs, t) → fmap (, t) vs)
  symbol "->"
  cod ← expr
  pure $ foldr (uncurry Π) cod doms

expr1 ∷ Parser Term
expr1 = Var  <$> ident
    <|> Type <$  symbol "*"
    <|> Hole <$  symbol "_"
    <|> parens expr

fnOrApp ∷ Parser Term
fnOrApp = do
  app ← foldl1' (:$) <$> some expr1
  optional (symbol "->") >>= \case
    Nothing → pure app
    Just _  → Π "" app <$> expr

expr ∷ Parser Term
expr = lam <$ symbol "\\"   <*> some binder
           <* symbol "."    <*> expr
   <|> Let <$ keyword "let" <*> binder
           <* symbol ":"    <*> expr
           <* symbol "="    <*> expr
           <* symbol "in"   <*> expr
   <|> try pi
   <|> fnOrApp
  where lam as b = foldr Λ b as

src ∷ Parser Term
src = sc *> expr <* eof
