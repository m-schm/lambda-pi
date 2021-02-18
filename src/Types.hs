module Types where

import Relude hiding (Type)

type Name = Text
type Type = Term

data Term
  = Var Name
  | Λ Name Term
  | Π Name Type Type
  | Term :$ Term
  | Let Name Type Term Term
  | Type
  deriving Show

data Val
  = VVar Name
  | Val :$$ ~Val
  | Vλ Name (Val → Val)
  | VΠ Name Val (Val → Val)
  | VType

type Env = [(Name, Val)]
