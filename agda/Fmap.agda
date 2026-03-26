module Fmap where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

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
n-comp : ∀ {a b c} → ncoe a b → ncoe b c → ncoe a c
na-comp :
  {a b u v x y : ty} →
  ncoe-arr a b u v →
  ncoe-arr u v x y →
  ncoe-arr a b x y
n-comp n n-id = n
n-comp (n-mono n1) (n-mono n2) = n-mono (n-comp n1 n2)
n-comp (n-arr na1) (n-arr na2) = n-arr (na-comp na1 na2)
na-comp (na-arr n1 n2) (na-arr n3 n4) =
  na-arr (n-comp n3 n1) (n-comp n2 n4)
na-comp na (na-fmap n) =
  na-fmap (na-comp na n)
na-comp {a} {b} {f u} {f v} {x} {y} (na-fmap n) na2 =
  na-comp n (na-fmap-l na2)

----------
-- EVAL --
----------
eval : {a b : ty} → coe a b → ncoe a b
eval (c-id a) = n-mkid a
eval (c-comp c1 c2) = n-comp (eval c1) (eval c2)
eval (c-arr c1 c2) = n-arr (na-arr (eval c1) (eval c2))
eval (c-mono c) = n-mono (eval c)
eval (c-fmap {a} {b}) = n-arr (na-fmap (na-mkid a b))

------------
-- PROOFS --
------------
------------------------------
-- Identity laws for n-comp --
------------------------------
n-comp-id-l : {a b : ty} (n : ncoe a b) →
  n-comp (n-mkid a) n ≡ n
n-comp-id-r : {a b : ty} (n : ncoe a b) →
  n-comp n (n-mkid b) ≡ n
na-comp-id-r : {a b u v : ty} (na : ncoe-arr a b u v) →
  na-comp na (na-mkid u v) ≡ na
na-comp-id-l : {a b u v : ty} (na : ncoe-arr a b u v) →
  na-comp (na-mkid a b) na ≡ na
na-comp-fmap-id-r : {a b u v : ty} → (na : ncoe-arr a b u v) →
  na-comp na (na-fmap (na-arr (n-mkid u) (n-mkid v))) ≡ na-fmap na
n-comp-id-l n-id = refl
n-comp-id-l (n-mono n) rewrite n-comp-id-l n = refl
n-comp-id-l (n-arr na) rewrite na-comp-id-l na = refl
n-comp-id-r n-id = refl
n-comp-id-r (n-mono n) rewrite n-comp-id-r n = refl
n-comp-id-r (n-arr na) rewrite na-comp-id-r na = refl
na-comp-id-l (na-arr n1 n2)
  rewrite n-comp-id-r n1
        | n-comp-id-l n2 = refl
na-comp-id-l (na-fmap na) rewrite na-comp-id-l na = refl
na-comp-id-r (na-arr n1 n2)
  rewrite n-comp-id-l n1
        | n-comp-id-r n2 = refl
na-comp-id-r (na-fmap na) = na-comp-fmap-id-r na
na-comp-fmap-id-r (na-arr n1 n2)
  rewrite n-comp-id-l n1
        | n-comp-id-r n2 = refl
na-comp-fmap-id-r (na-fmap na)
  rewrite na-comp-fmap-id-r na = refl

----------------------------
-- reifying mkid and comp --
----------------------------
reify-mkid : (a : ty) → reify (n-mkid a) ≃ c-id a
reify-mkid base = c-refl (c-id base)
reify-mkid (f a) = c-trans {f a} (c-cong-mono (reify-mkid a)) c-mono-id
reify-mkid (a ⇒ b) = c-trans (c-cong-arr (reify-mkid a) (reify-mkid b)) c-arr-id

reify-n-comp : {a b c : ty} (n1 : ncoe a b) (n2 : ncoe b c) →
  reify (n-comp n1 n2) ≃ c-comp (reify n1) (reify n2)
reify-na-comp : {a b u v x y : ty} (na1 : ncoe-arr a b u v) (na2 : ncoe-arr u v x y) →
  reify-arr (na-comp na1 na2) ≃ c-comp (reify-arr na1) (reify-arr na2)
reify-na-fmap-l : {a b u v : ty} (na : ncoe-arr (f a) (f b) u v) →
  reify-arr (na-fmap-l na) ≃ c-comp c-fmap (reify-arr na)

reify-n-comp n-id n2 rewrite n-comp-id-l n2 = c-sym c-id-l
reify-n-comp (n-mono n1) (n-mono n2) = c-trans (c-cong-mono (reify-n-comp n1 n2)) c-mono-comp
reify-n-comp (n-arr na1) (n-arr na2) = reify-na-comp na1 na2
reify-na-comp (na-arr n1 n2) (na-arr n3 n4) =
  c-trans (c-cong-arr (reify-n-comp n3 n1) (reify-n-comp n2 n4))
          c-arr-comp
reify-na-comp (na-arr n1 n2) (na-fmap na2) =
  c-trans (c-cong-comp (reify-na-comp (na-arr n1 n2) na2)
                       (c-refl c-fmap))
          c-comp-assoc
reify-na-comp (na-fmap na1) (na-arr n1 n2) =
  c-trans (reify-na-comp na1 (na-fmap-l (na-arr n1 n2)))
          (c-trans (c-cong-comp (c-refl _) (reify-na-fmap-l (na-arr n1 n2)))
                   (c-sym c-comp-assoc))
reify-na-comp (na-fmap na1) (na-fmap na2) =
  c-trans (c-cong-comp (reify-na-comp (na-fmap na1) na2) (c-refl _))
          c-comp-assoc
reify-na-fmap-l (na-arr (n-mono n1) (n-mono n2)) =
  c-sym c-arr-fmap -- ta daaa!
reify-na-fmap-l (na-fmap na) =
  c-trans (c-cong-comp (reify-na-fmap-l na) (c-refl _)) c-comp-assoc


------------------------------
-- REIFY-EVAL is id up to ≃ --
------------------------------
reify-eval : {a b : ty} (c : coe a b) → reify (eval c) ≃ c
reify-eval (c-id a) = reify-mkid a
reify-eval (c-comp c1 c2) =
  c-trans (reify-n-comp (eval c1) (eval c2))
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
countf : ty → ℕ
countf (f a) = suc (countf a)
countf _ = zero

-- for ncoe, countf is invariant
ncoe-countf : {a b : ty} → ncoe a b → countf a ≡ countf b
ncoe-countf n-id = refl
ncoe-countf (n-mono n) rewrite ncoe-countf n = refl
ncoe-countf (n-arr na) = refl

-- for ncoe-arr, countf is increasing (in the codomains)
ncoe-arr-countf : {a b u v : ty} → ncoe-arr a b u v → countf b ≤ countf v
ncoe-arr-countf (na-arr n1 n2) = ≤-reflexive (ncoe-countf n2)
ncoe-arr-countf (na-fmap na) = m≤n⇒m≤1+n (ncoe-arr-countf na)

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
  with ncoe-countf n2 | ncoe-arr-countf na
... | pf | h rewrite pf = contradiction h 1+n≰n
ncoe-arr-uniq (na-arr n1 n2) (na-fmap na)
  with ncoe-countf n2 | ncoe-arr-countf na
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
{- Could also do this the long way, but then you have to prove associativity of n-comp by hand (see the c-comp-assoc case).
eval-sound _ _ (c-refl c) = refl
eval-sound _ _ (c-sym pf) rewrite eval-sound _ _ pf = refl
eval-sound _ _ (c-trans pf1 pf2) rewrite eval-sound _ _ pf1 | eval-sound _ _ pf2 = refl
eval-sound _ _ (c-cong-comp pf1 pf2) rewrite eval-sound _ _ pf1 | eval-sound _ _ pf2 = refl
eval-sound _ _ (c-cong-arr pf1 pf2) rewrite eval-sound _ _ pf1 | eval-sound _ _ pf2 = refl
eval-sound _ _ (c-cong-mono pf) rewrite eval-sound _ _ pf = refl
eval-sound _ c2 c-id-l rewrite n-comp-id-l (eval c2) = refl
eval-sound _ c2 c-id-r rewrite n-comp-id-r (eval c2) = refl
eval-sound _ _ c-comp-assoc = {!!}
eval-sound _ _ c-mono-id = refl
eval-sound _ _ c-mono-comp = refl
eval-sound _ _ c-arr-id = refl
eval-sound _ _ c-arr-comp = refl
eval-sound _ (c-comp (c-arr c1 c2) (c-fmap)) c-arr-fmap
  rewrite n-comp-id-r (eval c1)
        | n-comp-id-l (eval c1)
        | n-comp-id-r (eval c2)
        | n-comp-id-l (eval c2) = refl
-}


--------------------------------
-- EVAL-REIFY is the identity --
--------------------------------
eval-reify : {a b : ty} (n : ncoe a b) → eval (reify n) ≡ n
eval-reify n = ncoe-uniq (eval (reify n)) n
{- here's a proof the long way...
eval-reify-arr : {a b u v : ty} (na : ncoe-arr a b u v) → eval (reify-arr na) ≡ n-arr na
eval-reify n-id = refl
eval-reify (n-mono n) rewrite eval-reify n = refl
eval-reify (n-arr na) = eval-reify-arr na
eval-reify-arr (na-arr n1 n2)
  rewrite eval-reify n1
        | eval-reify n2 = refl
eval-reify-arr (na-fmap na)
  rewrite eval-reify-arr na
        | na-comp-fmap-id-r na = refl
 -}

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
