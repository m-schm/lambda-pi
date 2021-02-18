module Check where

import Eval
import Types

import Relude

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
