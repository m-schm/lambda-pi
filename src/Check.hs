module Check where

import Eval
import Types

import Relude

type M = Either TypeError
data TypeError = Mismatch Val Val

report ∷ TypeError → M a
report = Left

conv ∷ Env → Val → Val → Bool
conv env = curry $ \case
  (VType, VType) → True
  (VΠ v_ t f, VΠ _ u g) →
    let v = fresh env $ "?" <> v_
    in conv env t u
    && conv ((v, VVar v):env) (f (VVar v)) (g (VVar v))
  (Vλ v_ f, Vλ _ g) →
    let v = fresh env $ "?" <> v_
    in conv ((v, VVar v):env) (f (VVar v)) (g (VVar v))
  (Vλ v_ f, x) →
    let v = fresh env $ "?" <> v_
    in conv ((v, VVar v):env) (f (VVar v)) (x :$$ VVar v)
  (x, Vλ v_ f) →
    let v = fresh env $ "?" <> v_
    in conv ((v, VVar v):env) (x :$$ VVar v) (f (VVar v))
  (VVar v, VVar v') → v == v'
  (f :$$ x, g :$$ y) → conv env f g && conv env x y
  (_, _) → False

check ∷ Env → Ctx → Term → VType → M ()
check env ctx = curry $ \case

  --    Γ, v:τ ⊢ e ⇐ f v
  -- -----------------------
  -- Γ ⊢ λv. e ⇐ ∀ v:τ. f v
  (Λ v e, VΠ v_ t f) →
    let v' = fresh env v_
    in check ((v, VVar v'):env) ((v, t):ctx) e (f (VVar v'))

  --        Γ ⊢ τ′ ⇐ *
  --        Γ ⊢ v ⇐ τ′
  --      Γ, v:τ′ ⊢ e ⇐ τ
  -- --------------------------
  -- Γ ⊢ let v:τ′ = x in e ⇐ τ
  (Let v t' x e, t) → do
    check env ctx t' VType
    let vt' = eval env t'
    check env ctx x vt'
    check ((v, eval env x):env) ((v, vt'):ctx) e t

  -- Γ ⊢ e ⇒ τ′
  -- Γ ⊢ τ ~ τ′
  -- -----------
  -- Γ ⊢ e ⇐ τ
  (e, t) → do
    it ← infer env ctx e
    unless (conv env t it) $
      report $ Mismatch t it

infer ∷ Env → Ctx → Term → M VType
infer = undefined
