module fmap.Decl where

open import Relation.Binary.PropositionalEquality

-----------
-- TYPES --
-----------
data ty : Set where
  base : ty
  f : ty → ty
  _⇒_ : ty → ty → ty

---------------
-- COERCIONS --
---------------
data coe : ty → ty → Set where
  c-id : (a : ty) → coe a a
  c-comp : {a b c : ty} → coe a b → coe b c → coe a c
  c-arr : {a b u v : ty} → coe u a → coe b v → coe (a ⇒ b) (u ⇒ v)
  c-mono : {a b : ty} → coe a b → coe (f a) (f b)
  c-fmap : {a b : ty} → coe (a ⇒ b) (f a ⇒ f b)

-- nice notation for c-comp
_·_ : {a b c : ty} → coe a b → coe b c → coe a c
c1 · c2 = c-comp c1 c2
infix 50 _·_

-- Laws for coercions
data _≃_ : {a b : ty} → coe a b → coe a b → Set where
  -- congruence laws
  c-refl : {a b : ty} (c : coe a b) → c ≃ c
  c-sym : {a b : ty} {c1 c2 : coe a b} → c1 ≃ c2 → c2 ≃ c1
  c-trans : {a b : ty} {c1 c2 c3 : coe a b} → c1 ≃ c2 → c2 ≃ c3 → c1 ≃ c3
  c-cong-comp : {a b c : ty} {c1 c1' : coe a b} {c2 c2' : coe b c} →
    c1 ≃ c1' → c2 ≃ c2' → c-comp c1 c2 ≃ c-comp c1' c2'
  c-cong-arr : {a b u v : ty} {c1 c1' : coe u a} {c2 c2' : coe b v} →
    c1 ≃ c1' → c2 ≃ c2' → c-arr c1 c2 ≃ c-arr c1' c2'
  c-cong-mono : {a b : ty} {c1 c2 : coe a b} →
    c1 ≃ c2 → c-mono c1 ≃ c-mono c2
  -- category and functor laws
  c-id-l : {a b : ty} {c : coe a b} → (c-id a · c) ≃ c
  c-id-r : {a b : ty} {c : coe a b} → (c · c-id b) ≃ c
  c-comp-assoc :
      {a b c d : ty}
      {c1 : coe a b}
      {c2 : coe b c}
      {c3 : coe c d} →
      (c1 · c2) · c3 ≃ c1 · (c2 · c3)
  c-mono-id : {a : ty} →
    c-mono (c-id a) ≃ c-id (f a)
  c-mono-comp : {a b c : ty} {c1 : coe a b} {c2 : coe b c} →
    c-mono (c1 · c2) ≃ c-mono c1 · c-mono c2
  c-arr-id : {a b : ty} →
    c-arr (c-id a) (c-id b) ≃ c-id (a ⇒ b)
  c-arr-comp : {a b c u v w : ty}
    {c1 : coe a b} {c2 : coe b c} {c3 : coe u v} {c4 : coe v w} →
    c-arr (c-comp c1 c2) (c-comp c3 c4) ≃ c-arr c2 c3 · c-arr c1 c4
  -- fmap law
  c-arr-fmap : {a b u v : ty} {c1 : coe a b} {c2 : coe u v} →
    c-fmap · c-arr (c-mono c1) (c-mono c2) ≃ c-arr c1 c2 · c-fmap

≡-to-≃ : {a b : ty} {c1 c2 : coe a b} → c1 ≡ c2 → c1 ≃ c2
≡-to-≃ {a} {b} {c} refl = c-refl c
