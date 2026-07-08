module Fmap where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation
open import Data.Product

id : {A : Set} → A → A
id x = x

_⨾_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
f ⨾ g = λ a → g (f a)
infixl 50 _⨾_

arr : {A B U V : Set} → (U → A) → (B → V) → ((A → B) → (U → V))
arr ua bv ab = ua ⨾ ab ⨾ bv

record Functor (F : Set → Set) : Set₁ where
  field fmap : {A B : Set} → (A → B) → (F A → F B)
  field fmap-id : ∀ {A} → fmap (id {A}) ≡ id {F A}
  field fmap-⨾ : ∀ {A B C} {f : A → B} {g : B → C} →
                   (fmap f ⨾ fmap g) ≡ fmap (f ⨾ g)

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

postulate
  funext : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

module interp {B : Set} {F : Set → Set} {FM : Functor F} where
  open Functor
  check : {A B : Set} → (A → B) → (F A → F B)
  check = fmap FM

  interp : ty → Set
  interp base = B
  interp (f a) = F (interp a)
  interp (a ⇒ b) = interp a → interp b

  interp-coe : {a b : ty} → coe a b → (interp a → interp b)
  interp-coe (c-id a) = id
  interp-coe (c-comp c1 c2) = interp-coe c1 ⨾ interp-coe c2
  interp-coe (c-arr c1 c2) = arr (interp-coe c1) (interp-coe c2)
  interp-coe (c-mono c) = fmap FM (interp-coe c)
  interp-coe c-fmap = fmap FM

  interp-sound : {a b : ty} → {c1 c2 : coe a b} → c1 ≃ c2 → interp-coe c1 ≡ interp-coe c2
  interp-sound (c-refl c) = refl
  interp-sound (c-sym pf) rewrite (interp-sound pf) = refl
  interp-sound (c-trans pf pf₁)
    rewrite interp-sound pf
          | interp-sound pf₁ = refl
  interp-sound (c-cong-comp pf pf₁)
    rewrite interp-sound pf
    rewrite interp-sound pf₁ = refl
  interp-sound (c-cong-arr pf pf₁)
    rewrite interp-sound pf
    rewrite interp-sound pf₁ = refl
  interp-sound (c-cong-mono pf)
    rewrite interp-sound pf = refl
  interp-sound c-id-l = refl
  interp-sound c-id-r = refl
  interp-sound c-comp-assoc = refl
  interp-sound c-mono-id = fmap-id FM 
  interp-sound c-mono-comp = sym (fmap-⨾ FM)
  interp-sound c-arr-id = refl
  interp-sound c-arr-comp = refl
  interp-sound (c-arr-fmap {c1 = c₁} {c2 = c₂}) = funext λ g →
    let ⟦c₁⟧ = interp-coe c₁
        ⟦c₂⟧ = interp-coe c₂
    in
    trans
      (cong (λ h → h ⨾ fmap FM ⟦c₂⟧)
        (fmap-⨾ FM {f = ⟦c₁⟧} {g = g}))
      (fmap-⨾ FM {f = ⟦c₁⟧ ⨾ g} {g = ⟦c₂⟧})


------------------
-- NORMAL FORMS --
------------------
data ncoe : ty → ty → Set
data ncoe-arr : ty → ty → ty → ty → Set
data ncoe where
  n-id : ncoe base base
  n-mono : ∀ {a b} → ncoe a b → ncoe (f a) (f b)
  n-arr : ∀ {a b u v} → ncoe-arr a b u v → ncoe (a ⇒ b) (u ⇒ v)
data ncoe-arr where
  na-arr : ∀ {a b u v} → ncoe u a → ncoe b v → ncoe-arr a b u v
  na-fmap : ∀ {a b u v} → ncoe-arr a b u v → ncoe-arr a b (f u) (f v)

-- (no laws needed since they're in normal form)

-----------
-- REIFY --
-----------
reify : ∀ {a b} → ncoe a b → coe a b
reify-arr : ∀ {a b u v} → ncoe-arr a b u v → coe (a ⇒ b) (u ⇒ v)
reify n-id = c-id base
reify (n-mono n) = c-mono (reify n)
reify (n-arr na) = reify-arr na
reify-arr (na-arr n1 n2) = c-arr (reify n1) (reify n2)
reify-arr (na-fmap na1) = reify-arr na1 · c-fmap

---------------
-- NF for ID --
---------------
-- this is the proof of reflexivity.
n-mkid : (a : ty) → ncoe a a
na-mkid : (a b : ty) → ncoe-arr a b a b
n-mkid base = n-id
n-mkid (f a) = n-mono (n-mkid a)
n-mkid (a ⇒ b) = n-arr (na-mkid a b)
na-mkid a b = na-arr (n-mkid a) (n-mkid b)

-----------------
-- NF for COMP --
-----------------
-- compose with an fmap on the left
-- (na-fmap composes with an fmap on the right)
-- this pushes the fmap through the coercion and is justified by c-arr-fmap
na-fmap-l :
  {a b u v : ty} →
  ncoe-arr (f a) (f b) u v →
  ncoe-arr a b u v
na-fmap-l (na-fmap na) =
  na-fmap (na-fmap-l na)
na-fmap-l {a} {b} {f u} {f v} (na-arr (n-mono n1) (n-mono n2)) =
  na-fmap (na-arr n1 n2)

-- composition operation
-- this is the proof of transitivity.
mkcomp : ∀ {a b c} → ncoe a b → ncoe b c → ncoe a c
mkcomp-na :
  {a b u v x y : ty} →
  ncoe-arr a b u v →
  ncoe-arr u v x y →
  ncoe-arr a b x y
mkcomp n n-id = n
mkcomp (n-mono n1) (n-mono n2) = n-mono (mkcomp n1 n2)
mkcomp (n-arr na1) (n-arr na2) = n-arr (mkcomp-na na1 na2)
mkcomp-na (na-arr n1 n2) (na-arr n3 n4) =
  na-arr (mkcomp n3 n1) (mkcomp n2 n4)
mkcomp-na na (na-fmap n) =
  na-fmap (mkcomp-na na n)
mkcomp-na {a} {b} {f u} {f v} {x} {y} (na-fmap n) na2 =
  mkcomp-na n (na-fmap-l na2)

----------
-- EVAL --
----------
eval : {a b : ty} → coe a b → ncoe a b
eval (c-id a) = n-mkid a
eval (c-comp c1 c2) = mkcomp (eval c1) (eval c2)
eval (c-arr c1 c2) = n-arr (na-arr (eval c1) (eval c2))
eval (c-mono c) = n-mono (eval c)
eval (c-fmap {a} {b}) = n-arr (na-fmap (na-mkid a b))

------------
-- PROOFS --
------------
------------------------------
-- Identity laws for n-comp --
------------------------------
mkcomp-id-l : {a b : ty} (n : ncoe a b) →
  mkcomp (n-mkid a) n ≡ n
mkcomp-id-r : {a b : ty} (n : ncoe a b) →
  mkcomp n (n-mkid b) ≡ n
mkcomp-na-id-r : {a b u v : ty} (na : ncoe-arr a b u v) →
  mkcomp-na na (na-mkid u v) ≡ na
mkcomp-na-id-l : {a b u v : ty} (na : ncoe-arr a b u v) →
  mkcomp-na (na-mkid a b) na ≡ na
mkcomp-na-fmap-id-r : {a b u v : ty} → (na : ncoe-arr a b u v) →
  mkcomp-na na (na-fmap (na-arr (n-mkid u) (n-mkid v))) ≡ na-fmap na
mkcomp-id-l n-id = refl
mkcomp-id-l (n-mono n) rewrite mkcomp-id-l n = refl
mkcomp-id-l (n-arr na) rewrite mkcomp-na-id-l na = refl
mkcomp-id-r n-id = refl
mkcomp-id-r (n-mono n) rewrite mkcomp-id-r n = refl
mkcomp-id-r (n-arr na) rewrite mkcomp-na-id-r na = refl
mkcomp-na-id-l (na-arr n1 n2)
  rewrite mkcomp-id-r n1
        | mkcomp-id-l n2 = refl
mkcomp-na-id-l (na-fmap na) rewrite mkcomp-na-id-l na = refl
mkcomp-na-id-r (na-arr n1 n2)
  rewrite mkcomp-id-l n1
        | mkcomp-id-r n2 = refl
mkcomp-na-id-r (na-fmap na) = mkcomp-na-fmap-id-r na
mkcomp-na-fmap-id-r (na-arr n1 n2)
  rewrite mkcomp-id-l n1
        | mkcomp-id-r n2 = refl
mkcomp-na-fmap-id-r (na-fmap na)
  rewrite mkcomp-na-fmap-id-r na = refl

----------------------------
-- reifying mkid and comp --
----------------------------
reify-mkid : (a : ty) → reify (n-mkid a) ≃ c-id a
reify-mkid base = c-refl (c-id base)
reify-mkid (f a) = c-trans {f a} (c-cong-mono (reify-mkid a)) c-mono-id
reify-mkid (a ⇒ b) = c-trans (c-cong-arr (reify-mkid a) (reify-mkid b)) c-arr-id

reify-na-fmap-l : {a b u v : ty} (na : ncoe-arr (f a) (f b) u v) →
  reify-arr (na-fmap-l na) ≃ c-comp c-fmap (reify-arr na)
reify-na-fmap-l (na-arr (n-mono n1) (n-mono n2)) =
  c-sym c-arr-fmap -- ta daaa!
reify-na-fmap-l (na-fmap na) =
  c-trans (c-cong-comp (reify-na-fmap-l na) (c-refl _)) c-comp-assoc

reify-mkcomp : {a b c : ty} (n1 : ncoe a b) (n2 : ncoe b c) →
  reify (mkcomp n1 n2) ≃ c-comp (reify n1) (reify n2)
reify-mkcomp-na : {a b u v x y : ty} (na1 : ncoe-arr a b u v) (na2 : ncoe-arr u v x y) →
  reify-arr (mkcomp-na na1 na2) ≃ c-comp (reify-arr na1) (reify-arr na2)

reify-mkcomp n-id n2 rewrite mkcomp-id-l n2 = c-sym c-id-l
reify-mkcomp (n-mono n1) (n-mono n2) = c-trans (c-cong-mono (reify-mkcomp n1 n2)) c-mono-comp
reify-mkcomp (n-arr na1) (n-arr na2) = reify-mkcomp-na na1 na2
reify-mkcomp-na (na-arr n1 n2) (na-arr n3 n4) =
  c-trans (c-cong-arr (reify-mkcomp n3 n1) (reify-mkcomp n2 n4))
          c-arr-comp
reify-mkcomp-na (na-arr n1 n2) (na-fmap na2) =
  c-trans (c-cong-comp (reify-mkcomp-na (na-arr n1 n2) na2)
                       (c-refl c-fmap))
          c-comp-assoc
reify-mkcomp-na (na-fmap na1) (na-arr n1 n2) =
  c-trans (reify-mkcomp-na na1 (na-fmap-l (na-arr n1 n2)))
          (c-trans (c-cong-comp (c-refl _) (reify-na-fmap-l (na-arr n1 n2)))
                   (c-sym c-comp-assoc))
reify-mkcomp-na (na-fmap na1) (na-fmap na2) =
  c-trans (c-cong-comp (reify-mkcomp-na (na-fmap na1) na2) (c-refl _))
          c-comp-assoc


------------------------------
-- REIFY-EVAL is id up to ≃ --
------------------------------
reify-eval : {a b : ty} (c : coe a b) → reify (eval c) ≃ c
reify-eval (c-id a) = reify-mkid a
reify-eval (c-comp c1 c2) =
  c-trans (reify-mkcomp (eval c1) (eval c2))
          (c-cong-comp (reify-eval c1) (reify-eval c2))
reify-eval (c-arr c1 c2) = c-cong-arr (reify-eval c1) (reify-eval c2)
reify-eval (c-mono c) = c-cong-mono (reify-eval c)
reify-eval (c-fmap {a} {b}) =
   c-trans (c-sym c-arr-fmap)
    (c-trans
      (c-cong-comp
        (c-refl c-fmap)
        (c-trans
          (c-cong-arr (c-trans (c-cong-mono (reify-mkid a)) c-mono-id)
                      (c-trans (c-cong-mono (reify-mkid b)) c-mono-id))
          c-arr-id))
      c-id-r)


------------------------------
-- COHERENCE AND UNIQUENESS --
------------------------------
-- counting leading uses of f in a type
peel : ty → ℕ
peel (f a) = suc (peel a)
peel _ = zero

-- for ncoe, peel is invariant
peel-inv : {a b : ty} → ncoe a b → peel a ≡ peel b
peel-inv n-id = refl
peel-inv (n-mono n) rewrite peel-inv n = refl
peel-inv (n-arr na) = refl

peel-inv-arr : {a b u v : ty} → ncoe-arr a b u v → Σ[ k ∈ ℕ ] (k + peel a ≡ peel u) × (k + peel b ≡ peel v)
peel-inv-arr (na-arr n₁ n₂)
  rewrite peel-inv n₁ | peel-inv n₂ = 0 , refl , refl
peel-inv-arr (na-fmap na)
  with peel-inv-arr na
...  | k , au , bv
  rewrite sym au | sym bv = suc k , refl , refl

-- for ncoe-arr, countf is increasing (in the codomains)
peel-le : {a b u v : ty} → ncoe-arr a b u v → peel b ≤ peel v
peel-le {a} {b} {u} {v} na with peel-inv-arr na
... | k , _ , bv rewrite sym bv = m≤n+m (peel b) k

-- Uniqueness of normalized coercions
ncoe-uniq : {a b : ty} (n1 n2 : ncoe a b) → n1 ≡ n2
ncoe-arr-uniq : {a b u v : ty} (na1 na2 : ncoe-arr a b u v) → na1 ≡ na2
ncoe-uniq n-id n-id = refl
ncoe-uniq (n-mono n1) (n-mono n2)
  rewrite ncoe-uniq n1 n2 = refl
ncoe-uniq (n-arr na1) (n-arr na2)
  rewrite ncoe-arr-uniq na1 na2 = refl
ncoe-arr-uniq (na-arr n1 n2) (na-arr n1' n2')
  rewrite ncoe-uniq n1 n1'
        | ncoe-uniq n2 n2' = refl
ncoe-arr-uniq (na-fmap na) (na-fmap na')
  rewrite ncoe-arr-uniq na na' = refl
ncoe-arr-uniq (na-fmap na) (na-arr (n-mono n1) (n-mono n2))
  with peel-inv n2 | peel-le na
... | pf | h rewrite pf = contradiction h 1+n≰n
ncoe-arr-uniq (na-arr n1 n2) (na-fmap na)
  with peel-inv n2 | peel-le na
... | pf | h rewrite pf = contradiction h 1+n≰n

-- Coherence of coercions
coe-coh : {a b : ty} (c1 c2 : coe a b) → c1 ≃ c2
coe-coh c1 c2 =
  c-trans (c-trans (c-sym (reify-eval c1))
                   (≡-to-≃ (cong reify (ncoe-uniq (eval c1) (eval c2)))))
          (reify-eval c2)

---------------------
-- EVAL RESPECTS ≃ --
---------------------
eval-sound : {a b : ty} (c1 c2 : coe a b) →
  c1 ≃ c2 → eval c1 ≡ eval c2
eval-sound c1 c2 _ = ncoe-uniq (eval c1) (eval c2)

--------------------------------
-- EVAL-REIFY is the identity --
--------------------------------
eval-reify : {a b : ty} (n : ncoe a b) → eval (reify n) ≡ n
eval-reify n = ncoe-uniq (eval (reify n)) n

-------------------
-- NORMALIZATION --
-------------------
norm : {a b : ty} → coe a b → coe a b
norm c = reify (eval c)

-- Normalization is idempotent.
norm-idem : {a b : ty} (c : coe a b) → norm (norm c) ≡ norm c
norm-idem c rewrite eval-reify (eval c) = refl -- this could be a use of ncoe-uniq too

-- Normalization is sound.
norm-sound : {a b : ty} (c1 c2 : coe a b) →
  c1 ≃ c2 → norm c1 ≡ norm c2
norm-sound c1 c2 sim rewrite eval-sound c1 c2 sim = refl -- this could be a use of ncoe-uniq too

-- Normalization is complete.
norm-complete : {a b : ty} (c1 c2 : coe a b) →
  norm c1 ≡ norm c2 → c1 ≃ c2
norm-complete c1 c2 neq =
  c-trans (c-sym (reify-eval c1))
    (c-trans (≡-to-≃ neq) (reify-eval c2))
