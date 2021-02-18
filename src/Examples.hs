module Examples (ex1, ex2, ex3) where

import Parse (src)
import Types (Term)

import Relude
import Text.Megaparsec (runParser)

parse ∷ Text → Term
parse = unsafeFromRight . runParser src ""
  where unsafeFromRight = either (error "oh jeez") id

ex1 ∷ Term
ex1 = parse "\
  \ let id : (A:*) -> A -> A = \\A x. x in \
  \ let foo : * = * in \
  \ id \
  \ "

ex2 ∷ Term
ex2 = parse "\
  \ let id : (A:*) -> A -> A = \\A x. x in \
  \ let const : (A B : *) -> A -> B -> A = \\_ _ x y. x in \
  \ id ((A B : *) -> A -> B -> A) const \
  \ "

ex3 ∷ Term
ex3 = parse "\
  \ let Nat : * = (N:*) -> (N -> N) -> N -> N in \
  \ let 5 : Nat = \\N s z. s (s (s (s (s z)))) in \
  \ let add : Nat -> Nat -> Nat = \
  \   \\a b N s z. a N s (b N s z) in \
  \ let mul : Nat -> Nat -> Nat = \
  \   \\a b N s z. a N (b N s) z in \
  \ let sqr : Nat -> Nat = \\a. mul a a in \
  \ let 10 : Nat = add 5 5 in \
  \ let 100 : Nat = mul 10 10 in \
  \ let 10k : Nat = sqr 100 in \
  \ 10k \
  \ "
