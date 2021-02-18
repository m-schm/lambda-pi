module Eval where

import Types

import Data.List (lookup)
import Relude

fresh ∷ Env → Name → Name
fresh _   "" = ""
fresh env n  = case lookup n env of
  Just _  → fresh env $ n <> "'"
  Nothing → n

eval ∷ Env → Term → Val
eval env = \case
  Var v       → fromMaybe (error $ "no variable: " <> v) $ lookup v env
  Λ v e       → Vλ v $ \x → eval ((v, x):env) e
  Π v t e     → VΠ v (eval env t) $ \x → eval ((v, x):env) e
  f :$ x      → case (eval env f, eval env x) of
    (Vλ _ f', x') → f' x'
    (f',      x') → f' :$$ x'
  Let v _ x e → eval ((v, eval env x):env) e
  Type        → VType

quote ∷ Env → Val → Term
quote env = \case
  VVar v   → Var v
  f :$$ x  → quote env f :$ quote env x
  Vλ v f   →
    let v' = fresh env v
    in Λ v' $ quote ((v', VVar v'):env) $ f (VVar v')
  VΠ v t f →
    let v' = fresh env v
    in Π v' (quote env t) $ quote ((v', VVar v'):env) $ f (VVar v')
  VType    → Type

nf ∷ Env → Term → Term
nf env = quote env . eval env
