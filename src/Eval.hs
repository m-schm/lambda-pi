module Eval where

import Types

import Prelude (lookup)
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

conv ∷ Env → Val → Val → Bool
conv env = curry $ \case
  (VType, VType) → True
  (VΠ v t f, VΠ _ u g) →
    let v' = fresh env $ "?" <> v
    in conv env t u
    && conv ((v', VVar v'):env) (f (VVar v')) (g (VVar v'))
  (Vλ v f, Vλ _ g) →
    let v' = fresh env $ "?" <> v
    in conv ((v', VVar v'):env) (f (VVar v')) (g (VVar v'))
  (Vλ v f, x) →
    let v' = fresh env $ "?" <> v
    in conv ((v', VVar v'):env) (f (VVar v')) (x :$$ VVar v')
  (x, Vλ v f) →
    let v' = fresh env $ "?" <> v
    in conv ((v', VVar v'):env) (x :$$ VVar v') (f (VVar v'))
  (VVar v, VVar v') → v == v'
  (f :$$ x, g :$$ y) → conv env f g && conv env x y
  (_, _) → False
