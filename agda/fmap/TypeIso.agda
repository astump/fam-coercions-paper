-- A bijection between algorithmic types and declarative types.

module fmap.TypeIso where
open import Relation.Binary.PropositionalEquality
open import Data.Product
import fmap.Algo as A
import fmap.Decl as D

reify-ty : A.ty → D.ty
reify-ty-F : A.ty-F → D.ty
reify-ty-noF : A.ty-noF → D.ty
reify-ty-arr : A.ty-arr → D.ty × D.ty

reify-ty (A.ty-ty-F t) = reify-ty-F t
reify-ty (A.ty-ty-noF t) = reify-ty-noF t
reify-ty-F (A.ty-F-F t) = D.f (reify-ty-F t)
reify-ty-F (A.ty-F-noF t) = D.f (reify-ty-noF t)
reify-ty-noF A.nt-bool = D.base
reify-ty-noF (A.nt-arr t) with reify-ty-arr t
reify-ty-noF (A.nt-arr t) | t₁ , t₂ = t₁ D.⇒ t₂
reify-ty-arr (A.ty-arr-lift t) with reify-ty-arr t
reify-ty-arr (A.ty-arr-lift t) | t₁ , t₂ = D.f t₁ , D.f t₂
reify-ty-arr (A.ty-arr-l t₁ t₂) = reify-ty-F t₁ , reify-ty-noF t₂
reify-ty-arr (A.ty-arr-r t₁ t₂) = reify-ty-noF t₁ , reify-ty-F t₂
reify-ty-arr (A.ty-arr-arr t₁ t₂) = reify-ty-noF t₁ , reify-ty-noF t₂

eval-ty : D.ty → A.ty
eval-ty-F : D.ty → A.ty-F
eval-ty-arr : D.ty → D.ty → A.ty-arr

eval-ty D.base = A.ty-ty-noF (A.nt-bool)
eval-ty (D.f t) = A.ty-ty-F (eval-ty-F t)
eval-ty (t₁ D.⇒ t₂) = A.ty-ty-noF (A.nt-arr (eval-ty-arr t₁ t₂))

eval-ty-arr (D.f t₁) (D.f t₂) = A.ty-arr-lift (eval-ty-arr t₁ t₂)
eval-ty-arr (D.f t) D.base = A.ty-arr-l (eval-ty-F t) A.nt-bool
eval-ty-arr (D.f t) (t₁ D.⇒ t₂) =
  A.ty-arr-l (eval-ty-F t)
             (A.nt-arr (eval-ty-arr t₁ t₂))
eval-ty-arr D.base (D.f t) =
  A.ty-arr-r A.nt-bool (eval-ty-F t)
eval-ty-arr (t₁ D.⇒ t₂) (D.f t) =
  A.ty-arr-r (A.nt-arr (eval-ty-arr t₁ t₂)) (eval-ty-F t)
eval-ty-arr D.base D.base = A.ty-arr-arr A.nt-bool A.nt-bool
eval-ty-arr D.base (t₁ D.⇒ t₂) =
  A.ty-arr-arr
    A.nt-bool
    (A.nt-arr (eval-ty-arr t₁ t₂))
eval-ty-arr (t₁ D.⇒ t₂) D.base =
  A.ty-arr-arr
    (A.nt-arr (eval-ty-arr t₁ t₂))
    A.nt-bool
eval-ty-arr (t₁ D.⇒ t₂) (t₃ D.⇒ t₄) =
  A.ty-arr-arr (A.nt-arr (eval-ty-arr t₁ t₂))
               (A.nt-arr (eval-ty-arr t₃ t₄))
eval-ty-F (D.f t) = A.ty-F-F (eval-ty-F t)
eval-ty-F D.base = A.ty-F-noF A.nt-bool
eval-ty-F (t₁ D.⇒ t₂) = A.ty-F-noF (A.nt-arr (eval-ty-arr t₁ t₂))


----------------
-- eval-reify --
----------------

eval-reify-ty-F : (t : D.ty) → reify-ty-F (eval-ty-F t) ≡ D.f t
eval-reify-ty-arr : (a b : D.ty) → (reify-ty-arr (eval-ty-arr a b)) ≡ (a , b)

eval-reify-ty-F D.base = refl
eval-reify-ty-F (D.f t) rewrite eval-reify-ty-F t = refl
eval-reify-ty-F (a D.⇒ b) rewrite eval-reify-ty-arr a b = refl

eval-reify-ty-arr D.base D.base = refl
eval-reify-ty-arr D.base (D.f b) rewrite eval-reify-ty-F b = refl
eval-reify-ty-arr D.base (b D.⇒ b') rewrite eval-reify-ty-arr b b' = refl
eval-reify-ty-arr (D.f a) D.base rewrite eval-reify-ty-F a = refl
eval-reify-ty-arr (D.f a) (D.f b) rewrite eval-reify-ty-arr a b = refl
eval-reify-ty-arr (D.f a) (b D.⇒ b')
  rewrite eval-reify-ty-F a
        | eval-reify-ty-arr b b' = refl
eval-reify-ty-arr (a D.⇒ a') D.base rewrite eval-reify-ty-arr a a' = refl
eval-reify-ty-arr (a D.⇒ a') (D.f b)
  rewrite eval-reify-ty-arr a a'
          | eval-reify-ty-F b = refl
eval-reify-ty-arr (a D.⇒ a') (b D.⇒ b')
  rewrite eval-reify-ty-arr a a'
        | eval-reify-ty-arr b b' = refl

eval-reify-ty : (t : D.ty) → reify-ty (eval-ty t) ≡ t
eval-reify-ty D.base = refl
eval-reify-ty (D.f t) = eval-reify-ty-F t
eval-reify-ty (t₁ D.⇒ t₂) rewrite (eval-reify-ty-arr t₁ t₂) = refl

----------------
-- reify-eval --
----------------

reify-eval-ty : (t : A.ty) → (eval-ty (reify-ty t)) ≡ t
reify-eval-ty-F : (t : A.ty-F) → (eval-ty-F (reify-ty-F t)) ≡ A.ty-F-F t
reify-eval-ty-F-noF : (t : A.ty-noF) → (eval-ty-F (reify-ty-noF t)) ≡ A.ty-F-noF t
reify-eval-ty-noF : (t : A.ty-noF) → (eval-ty (reify-ty-noF t)) ≡ A.ty-ty-noF t
reify-eval-arr : (a : A.ty-arr) → eval-ty-arr (reify-ty-arr a .proj₁) (reify-ty-arr a .proj₂) ≡ a

reify-eval-ty (A.ty-ty-F (A.ty-F-F a)) rewrite reify-eval-ty-F a = refl
reify-eval-ty (A.ty-ty-F (A.ty-F-noF a)) rewrite reify-eval-ty-F-noF a = refl
reify-eval-ty (A.ty-ty-noF a) rewrite reify-eval-ty-noF a = refl

reify-eval-ty-F (A.ty-F-F a) rewrite reify-eval-ty-F a = refl
reify-eval-ty-F (A.ty-F-noF a) rewrite reify-eval-ty-F-noF a = refl

reify-eval-ty-F-noF A.nt-bool = refl
reify-eval-ty-F-noF (A.nt-arr a) rewrite reify-eval-arr a = refl

reify-eval-ty-noF A.nt-bool = refl
reify-eval-ty-noF (A.nt-arr a) rewrite reify-eval-arr a = refl

reify-eval-arr (A.ty-arr-lift a) rewrite reify-eval-arr a = refl
reify-eval-arr (A.ty-arr-l (A.ty-F-F a) A.nt-bool)
  rewrite reify-eval-ty-F a = refl
reify-eval-arr (A.ty-arr-l (A.ty-F-F a) (A.nt-arr b))
  rewrite reify-eval-ty-F a | reify-eval-arr b = refl
reify-eval-arr (A.ty-arr-l (A.ty-F-noF a) A.nt-bool)
  rewrite reify-eval-ty-F-noF a = refl
reify-eval-arr (A.ty-arr-l (A.ty-F-noF a) (A.nt-arr b))
  rewrite reify-eval-ty-F-noF a | reify-eval-arr b = refl
reify-eval-arr (A.ty-arr-r A.nt-bool (A.ty-F-F b))
  rewrite reify-eval-ty-F b = refl
reify-eval-arr (A.ty-arr-r A.nt-bool (A.ty-F-noF b))
  rewrite reify-eval-ty-F-noF b = refl
reify-eval-arr (A.ty-arr-r (A.nt-arr a) (A.ty-F-F b))
  rewrite reify-eval-arr a | reify-eval-ty-F b = refl
reify-eval-arr (A.ty-arr-r (A.nt-arr a) (A.ty-F-noF b))
  rewrite reify-eval-arr a | reify-eval-ty-F-noF b = refl
reify-eval-arr (A.ty-arr-arr A.nt-bool A.nt-bool) = refl
reify-eval-arr (A.ty-arr-arr A.nt-bool (A.nt-arr b))
  rewrite reify-eval-arr b = refl
reify-eval-arr (A.ty-arr-arr (A.nt-arr a) A.nt-bool)
  rewrite reify-eval-arr a = refl
reify-eval-arr (A.ty-arr-arr (A.nt-arr a) (A.nt-arr b))
  rewrite reify-eval-arr a | reify-eval-arr b = refl
