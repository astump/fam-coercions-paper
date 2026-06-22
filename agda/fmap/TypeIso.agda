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


mk-ty-arr : A.ty → A.ty → A.ty-arr
mk-ty-arr-F-F : A.ty-F → A.ty-F → A.ty-arr
mk-ty-arr (A.ty-ty-F a) (A.ty-ty-F b) = A.ty-arr-lift (mk-ty-arr-F-F a b)
mk-ty-arr (A.ty-ty-F a) (A.ty-ty-noF b) = A.ty-arr-l a b
mk-ty-arr (A.ty-ty-noF a) (A.ty-ty-F b) = A.ty-arr-r a b
mk-ty-arr (A.ty-ty-noF a) (A.ty-ty-noF b) = A.ty-arr-arr a b
mk-ty-arr-F-F (A.ty-F-F a) (A.ty-F-F b) = A.ty-arr-lift (mk-ty-arr-F-F a b)
mk-ty-arr-F-F (A.ty-F-F a) (A.ty-F-noF b) = A.ty-arr-l a b
mk-ty-arr-F-F (A.ty-F-noF a) (A.ty-F-F b) = A.ty-arr-r a b
mk-ty-arr-F-F (A.ty-F-noF a) (A.ty-F-noF b) = A.ty-arr-arr a b

eval-ty : D.ty → A.ty
eval-ty-F : D.ty → A.ty-F
eval-ty-arr : D.ty → D.ty → A.ty-arr

eval-ty D.base = A.ty-ty-noF (A.nt-bool)
eval-ty (D.f t) = A.ty-ty-F (eval-ty-F t)
eval-ty (t₁ D.⇒ t₂) = A.ty-ty-noF (A.nt-arr (eval-ty-arr t₁ t₂))

eval-ty-arr a b = mk-ty-arr (eval-ty a) (eval-ty b)
eval-ty-F (D.f t) = A.ty-F-F (eval-ty-F t)
eval-ty-F D.base = A.ty-F-noF A.nt-bool
eval-ty-F (t₁ D.⇒ t₂) = A.ty-F-noF (A.nt-arr (eval-ty-arr t₁ t₂))


----------------
-- eval-reify --
----------------

eval-reify-ty-F : (t : D.ty) → reify-ty-F (eval-ty-F t) ≡ D.f t
eval-reify-ty-arr : (a b : D.ty) → (reify-ty-arr (eval-ty-arr a b)) ≡ (a , b)
reify-ty-arr-F-F : (a b : D.ty) → reify-ty-arr (mk-ty-arr-F-F (eval-ty-F a) (eval-ty-F b)) ≡ (a , b)

eval-reify-ty-F D.base = refl
eval-reify-ty-F (D.f t) rewrite eval-reify-ty-F t = refl
eval-reify-ty-F (a D.⇒ b) rewrite eval-reify-ty-arr a b = refl

eval-reify-ty-arr D.base D.base = refl
eval-reify-ty-arr D.base (D.f b) rewrite eval-reify-ty-F b = refl
eval-reify-ty-arr D.base (b D.⇒ b₁) rewrite eval-reify-ty-arr b b₁ = refl
eval-reify-ty-arr (D.f a) D.base rewrite eval-reify-ty-F a = refl
eval-reify-ty-arr (D.f a) (D.f b) rewrite reify-ty-arr-F-F a b = refl
eval-reify-ty-arr (D.f a) (b D.⇒ b₁)
  rewrite eval-reify-ty-F a
        | eval-reify-ty-arr b b₁ = refl
eval-reify-ty-arr (a D.⇒ a₁) D.base
  rewrite eval-reify-ty-arr a a₁ = refl
eval-reify-ty-arr (a D.⇒ a₁) (D.f b)
  rewrite eval-reify-ty-arr a a₁
        | eval-reify-ty-F b = refl
eval-reify-ty-arr (a D.⇒ a₁) (b D.⇒ b₁)
  rewrite eval-reify-ty-arr a a₁
        | eval-reify-ty-arr b b₁ = refl

reify-ty-arr-F-F D.base D.base = refl
reify-ty-arr-F-F D.base (D.f b) rewrite eval-reify-ty-F b = refl
reify-ty-arr-F-F D.base (b D.⇒ b₁) rewrite eval-reify-ty-arr b b₁ = refl
reify-ty-arr-F-F (D.f a) D.base rewrite eval-reify-ty-F a = refl
reify-ty-arr-F-F (D.f a) (D.f b) rewrite reify-ty-arr-F-F a b = refl
reify-ty-arr-F-F (D.f a) (b D.⇒ b₁)
  rewrite eval-reify-ty-F a
        | eval-reify-ty-arr b b₁ = refl
reify-ty-arr-F-F (a D.⇒ a₁) D.base
  rewrite eval-reify-ty-arr a a₁ = refl
reify-ty-arr-F-F (a D.⇒ a₁) (D.f b)
  rewrite eval-reify-ty-arr a a₁
        | eval-reify-ty-F b = refl
reify-ty-arr-F-F (a D.⇒ a₁) (b D.⇒ b₁)
  rewrite eval-reify-ty-arr a a₁
        | eval-reify-ty-arr b b₁ = refl

eval-reify-ty : (t : D.ty) → reify-ty (eval-ty t) ≡ t
eval-reify-ty D.base = refl
eval-reify-ty (D.f t) = eval-reify-ty-F t
eval-reify-ty (t₁ D.⇒ t₂) rewrite (eval-reify-ty-arr t₁ t₂) = refl

----------------
-- reify-eval --
----------------

reify-eval-ty : (t : A.ty) → (eval-ty (reify-ty t)) ≡ t
reify-eval-ty-F : (t : A.ty-F) → (eval-ty-F (reify-ty-F t)) ≡ A.ty-F-F t
reify-eval-ty-F' : (t : A.ty-F) → (eval-ty (reify-ty-F t)) ≡ A.ty-ty-F t
reify-eval-ty-F-noF : (t : A.ty-noF) → (eval-ty-F (reify-ty-noF t)) ≡ A.ty-F-noF t
reify-eval-ty-noF : (t : A.ty-noF) → (eval-ty (reify-ty-noF t)) ≡ A.ty-ty-noF t
reify-eval-arr : (a : A.ty-arr) →
 mk-ty-arr (eval-ty (reify-ty-arr a .proj₁)) (eval-ty (reify-ty-arr a .proj₂)) ≡ a
reify-eval-arr-F-F : (a : A.ty-arr) →
 mk-ty-arr-F-F (eval-ty-F (reify-ty-arr a .proj₁)) (eval-ty-F (reify-ty-arr a .proj₂)) ≡ a

reify-eval-ty (A.ty-ty-F (A.ty-F-F a)) rewrite reify-eval-ty-F a = refl
reify-eval-ty (A.ty-ty-F (A.ty-F-noF a)) rewrite reify-eval-ty-F-noF a = refl
reify-eval-ty (A.ty-ty-noF a) rewrite reify-eval-ty-noF a = refl

reify-eval-ty-F (A.ty-F-F a) rewrite reify-eval-ty-F a = refl
reify-eval-ty-F (A.ty-F-noF a) rewrite reify-eval-ty-F-noF a = refl

reify-eval-ty-F' (A.ty-F-F t) rewrite reify-eval-ty-F t = refl
reify-eval-ty-F' (A.ty-F-noF t) rewrite reify-eval-ty-F-noF t = refl

reify-eval-ty-F-noF A.nt-bool = refl
reify-eval-ty-F-noF (A.nt-arr a) rewrite reify-eval-arr a = refl

reify-eval-ty-noF A.nt-bool = refl
reify-eval-ty-noF (A.nt-arr a) rewrite reify-eval-arr a = refl

reify-eval-arr (A.ty-arr-lift a) rewrite reify-eval-arr-F-F a = refl
reify-eval-arr (A.ty-arr-l a b)
  rewrite reify-eval-ty-F' a
        | reify-eval-ty-noF b = refl
reify-eval-arr (A.ty-arr-r a b)
  rewrite reify-eval-ty-noF a
        | reify-eval-ty-F' b = refl
reify-eval-arr (A.ty-arr-arr a b)
  rewrite reify-eval-ty-noF a
        | reify-eval-ty-noF b = refl

reify-eval-arr-F-F (A.ty-arr-lift a) rewrite reify-eval-arr-F-F a = refl
reify-eval-arr-F-F (A.ty-arr-l a b)
  rewrite reify-eval-ty-F a
        | reify-eval-ty-F-noF b = refl
reify-eval-arr-F-F (A.ty-arr-r a b)
  rewrite reify-eval-ty-F b
        | reify-eval-ty-F-noF a = refl
reify-eval-arr-F-F (A.ty-arr-arr a b)
  rewrite reify-eval-ty-F-noF a
        | reify-eval-ty-F-noF b = refl


-- A relational formulation of the isomorphism.
-- TODO: prove that this relation is the graph of reify-ty.
data repr-ty : A.ty → D.ty → Set
data repr-ty-F : A.ty-F → D.ty → Set
data repr-ty-noF : A.ty-noF → D.ty → Set
data repr-ty-arr : A.ty-arr → D.ty → D.ty → Set

data repr-ty where
  repr-ty-ty-F : ∀ {a d} → repr-ty-F a d → repr-ty (A.ty-ty-F a) (D.f d)
  repr-ty-ty-noF : ∀ {a d} → repr-ty-noF a d → repr-ty (A.ty-ty-noF a) d

data repr-ty-F where
  repr-ty-F-F : ∀ {a d} → repr-ty-F a d → repr-ty-F (A.ty-F-F a) (D.f d)
  repr-ty-F-noF : ∀ {a d} → repr-ty-noF a d → repr-ty-F (A.ty-F-noF a) d

data repr-ty-noF where
  repr-ty-noF-bool : repr-ty-noF A.nt-bool D.base
  repr-ty-noF-arr : ∀ {a d₁ d₂} → repr-ty-arr a d₁ d₂ → repr-ty-noF (A.nt-arr a) (d₁ D.⇒ d₂)

data repr-ty-arr where
  repr-ty-arr-lift : ∀ {a d₁ d₂} →
    repr-ty-arr a d₁ d₂ →
    repr-ty-arr (A.ty-arr-lift a) (D.f d₁) (D.f d₂)
  repr-ty-arr-l : ∀ {a₁ a₂ d₁ d₂} →
    repr-ty-F a₁ d₁ →
    repr-ty-noF a₂ d₂ →
    repr-ty-arr (A.ty-arr-l a₁ a₂) (D.f d₁) d₂
  repr-ty-arr-r : ∀ {a₁ a₂ d₁ d₂} →
    repr-ty-noF a₁ d₁ →
    repr-ty-F a₂ d₂ →
    repr-ty-arr (A.ty-arr-r a₁ a₂) d₁ (D.f d₂)
  repr-ty-arr-arr : ∀ {a₁ a₂ d₁ d₂} →
    repr-ty-noF a₁ d₁ →
    repr-ty-noF a₂ d₂ →
    repr-ty-arr (A.ty-arr-arr a₁ a₂) d₁ d₂
