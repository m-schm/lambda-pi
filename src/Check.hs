module Check where

import Eval
import Types

import Data.List (lookup)
import Relude

type M = Either TypeError
data TypeError
  = Mismatch Term Term
  | CantInferLambda
  | UnknownName Name
  | NotPi Term
  deriving Show

report ∷ TypeError → M a
report = Left

conv ∷ Env → Val → Val → Bool
conv env = curry $ \case

  -- ---------
  -- Γ ⊢ * ~ *
  (VType, VType) → True

  --         Γ ⊢ σ₁ ~ σ₂
  --      Γ, x:σᵢ ⊢ τ₁ ~ τ₂
  -- ---------------------------
  -- Γ ⊢ ∀ x:σ₁. τ₁ ~ ∀ x:σ₂. τ₂
  (VΠ v_ t f, VΠ _ u g) →
    let v = fresh env $ "?" <> v_
    in conv env t u
    && conv ((v, VVar v):env) (f (VVar v)) (g (VVar v))

  --   Γ, v ⊢ e₁ ~ e₂
  -- -------------------
  -- Γ ⊢ λv. e₁ ~ λv. e₂
  (Vλ v_ f, Vλ _ g) →
    let v = fresh env $ "?" <> v_
    in conv ((v, VVar v):env) (f (VVar v)) (g (VVar v))

  -- Γ, v ⊢ e₁ ~ e₂ v
  -- ----------------
  -- Γ ⊢ λv. e₁ ~ e₂
  (Vλ v_ f, x) →
    let v = fresh env $ "?" <> v_
    in conv ((v, VVar v):env) (f (VVar v)) (x :$$ VVar v)
  (x, Vλ v_ f) →
    let v = fresh env $ "?" <> v_
    in conv ((v, VVar v):env) (x :$$ VVar v) (f (VVar v))

  --   v₁ = v₂
  -- -----------
  -- Γ ⊢ v₁ ~ v₂
  (VVar v, VVar v') → v == v'

  --    Γ ⊢ f₁ ~ f₂
  --    Γ ⊢ x₁ ~ x₂
  -- -----------------
  -- Γ ⊢ f₁ x₁ ~ f₂ x₂
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
      report $ Mismatch (quote env t) (quote env it)

infer ∷ Env → Ctx → Term → M VType
infer env ctx = \case

  -- v : τ ∈ Γ
  -- ----------
  -- Γ ⊢ v ⇒ τ
  Var v → case lookup v ctx of
    Nothing → report $ UnknownName v
    Just t  → pure t

  -- ----------
  -- Γ ⊢ * ⇒ *
  Type → pure VType

  -- Γ ⊢ f ⇒ ∀ a:τ. τ′
  --     Γ ⊢ x ⇐ τ
  -- ------------------
  -- Γ ⊢ f x ⇒ τ′[x/a]
  f :$ x → infer env ctx f >>= \case
    VΠ _ t g → do
      check env ctx x t
      pure $ g (eval env x)
    t → report $ NotPi (quote env t)

  Λ _ _ → report CantInferLambda

  --     Γ ⊢ τ ⇐ *
  --  Γ, v:τ ⊢ τ′ ⇐ *
  -- ------------------
  -- Γ ⊢ ∀ v:τ. τ′ ⇒ *
  Π v t e → do
    check env ctx t VType
    check ((v, VVar v):env) ((v, eval env t):ctx) e VType
    pure VType

  --        Γ ⊢ τ′ ⇐ *
  --        Γ ⊢ x ⇐ τ′
  --     Γ, v:τ′ ⊢ e ⇒ τ
  -- -------------------------
  -- Γ ⊢ let v:τ′ = x in e ⇒ τ
  Let v t x e → do
    check env ctx t VType
    let vt = eval env t
    check env ctx x vt
    infer ((v, eval env x):env) ((v, vt):ctx) e
