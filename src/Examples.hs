module Examples (ex1, ex2, ex3, ex4) where

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
  \ let _ : * = * in \
  \ id \
  \ "

ex2 ∷ Term
ex2 = parse "\
  \ let id : (A:*) -> A -> A = \\_ x. x in \
  \ let const : (A B : *) -> A -> B -> A = \\_ _ x y. x in \
  \ id _ const \
  \ "

ex3 ∷ Term
ex3 = parse "\
  \ let Nat : * = (N:*) -> (N -> N) -> N -> N in \
  \ let 5 : Nat = \\_ s z. s (s (s (s (s z)))) in \
  \ let add : Nat -> Nat -> Nat = \
  \   \\a b _ s z. a _ s (b _ s z) in \
  \ let mul : Nat -> Nat -> Nat = \
  \   \\a b _ s z. a _ (b _ s) z in \
  \ let join : (A B : *) -> (A -> A -> B) -> A -> B = \
  \   \\_ _ f x. f x x in \
  \ let 10 : Nat = join _ _ add 5 in \
  \ let sqr : Nat -> Nat = join _ _ mul in \
  \ let 100 : Nat = sqr 10 in \
  \ let 10k : Nat = sqr 100 in \
  \ 10k \
  \ "

ex4 ∷ Term
ex4 = parse "\
  \ let List : * -> * = \\A. (L:*) -> (A->L->L) -> L -> L in \
  \ let cons : (A:*) -> A -> List A -> List A = \
  \   \\_ x xs L c n -> c x (xs _ c n) in \
  \ let nil : (A:*) -> List A = \\_ _ _ n. n in \
  \ cons _ * (cons _ * (nil _)) \
  \ "
