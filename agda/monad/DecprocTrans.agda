module DecprocTrans where

open import lib
open import Tp
open import Decproc

-- Transitivity is admissible

size : ∀{T T' : Tp!} → T <:! T' → ℕ
size (Nat<! x) = 0
size (Fun<! x d d₁) = suc (size d) + (size d₁)

-- completeness for cov
cov! : ∀ {A B : Tp!} → A <:! B → ↑ A <:! ↑ B
cov! (Nat<! ok) =
  Nat<! refl
cov! (Fun<! {q = tt} ok dom cod) =
  Fun<! {q = tt} refl dom cod
cov! (Fun<! {q = ff} ok dom cod) =
  Fun<! {q = ff} refl dom cod

-- cov preserves size
size-cov! : ∀ {A B : Tp!} → (d : A <:! B) → size (cov! d) ≡ size d
size-cov! (Nat<! ok) = refl
size-cov! (Fun<! {q = tt} ok dom cod) = refl
size-cov! (Fun<! {q = ff} ok dom cod) = refl

↑-pull-dom : ∀{A' A : Tp!} →
  A' <:! ↑ A →
  ↑ A' <:! ↑ A
↑-pull-dom {x !N} {x₁ !N} (Nat<! x₂) = Nat<! refl
↑-pull-dom {x ! A' ⇒ A''} {x₁ ! A ⇒ A₁} (Fun<!{q} x₂ d d₁) = Fun<!{q} (funOK-tt-tt{q}{tt}) d d₁

-- ↑-pull-dom preserves size
size-↑-pull-dom : ∀{A' A : Tp!} → (d : A' <:! ↑ A) → size (↑-pull-dom d) ≡ size d
size-↑-pull-dom {x !N} {x₁ !N} (Nat<! ok) = refl
size-↑-pull-dom {x ! A' ⇒ A''} {x₁ ! A ⇒ A₁} (Fun<!{q} ok dom cod) = refl

↑-pull-codom : ∀{A' A : Tp!} →
  ↑ A <:! A' →
  ↑ A <:! ↑ A'
↑-pull-codom {x !N} {x₁ !N} (Nat<! x₂) = Nat<! refl
↑-pull-codom {x ! A ⇒ A₁} {x₁ ! A' ⇒ A''} (Fun<!{q} x₂ d d₁) = Fun<!{q} (funOK-tt-tt{q}{tt}) d d₁

-- ↑-pull-codom preserves size
size-↑-pull-codom : ∀{A' A : Tp!} → (d : ↑ A <:! A') → size (↑-pull-codom d) ≡ size d
size-↑-pull-codom {x !N} {x₁ !N} (Nat<! ok) = refl
size-↑-pull-codom {x ! A ⇒ A₁} {x₁ ! A' ⇒ A''} (Fun<!{q} ok dom cod) = refl

layerOK-trans : ∀ (b₁ b₂ b₃ : 𝔹) →
                layerOK b₁ b₂ ≡ tt →
                layerOK b₂ b₃ ≡ tt →
                layerOK b₁ b₃ ≡ tt
layerOK-trans ff b₂    b₃    p q = refl
layerOK-trans tt  ff b₃    ()
layerOK-trans tt  tt  ff p ()
layerOK-trans tt  tt  tt  p q = refl

-- AI Generated
trans-fuel-dom : ∀ {n : ℕ} (a b c d : ℕ) →
                 (suc a + b) + (suc c + d) ≤ suc n ≡ tt →
                 c + a ≤ n ≡ tt
trans-fuel-dom {n = n} a b c d u =
  <≤ {n = c + a} {m = n}
     (≤<-trans {x = c + a} {y = (a + b) + (c + d)} {z = n} ca≤sum sum<n)
  where
    u' : (a + b) + suc (c + d) ≤ n ≡ tt
    u' = suc≤ {n = (a + b) + suc (c + d)} {n' = n} u
    u'' : suc ((a + b) + (c + d)) ≤ n ≡ tt
    u'' = cong-pred (λ x → x ≤ n ≡ tt) (+suc (a + b) (c + d)) u'
    sum<n : (a + b) + (c + d) < n ≡ tt
    sum<n = suc≤< {n = (a + b) + (c + d)} {n' = n} u''
    step1 : a + c ≤ (a + b) + c ≡ tt
    step1 = ≤+mono1 {x = a} {x' = a + b} {y = c} (≤+1 a b)
    step2 : (a + b) + c ≤ (a + b) + (c + d) ≡ tt
    step2 = ≤+mono2 {x = a + b} {y = c} {y' = c + d} (≤+1 c d)
    ac≤sum : a + c ≤ (a + b) + (c + d) ≡ tt
    ac≤sum = ≤-trans {x = a + c} {y = (a + b) + c} {z = (a + b) + (c + d)} step1 step2
    ca≤sum : c + a ≤ (a + b) + (c + d) ≡ tt
    ca≤sum = cong-pred (λ x → x ≤ (a + b) + (c + d) ≡ tt) (+comm a c) ac≤sum

-- AI Generated
trans-fuel-cod : ∀ {n : ℕ} (a b c d : ℕ) →
                 (suc a + b) + (suc c + d) ≤ suc n ≡ tt →
                 b + d ≤ n ≡ tt
trans-fuel-cod {n = n} a b c d u =
  <≤ {n = b + d} {m = n}
     (≤<-trans {x = b + d} {y = (a + b) + (c + d)} {z = n} bd≤sum sum<n)
  where
    u' : (a + b) + suc (c + d) ≤ n ≡ tt
    u' = suc≤ {n = (a + b) + suc (c + d)} {n' = n} u
    u'' : suc ((a + b) + (c + d)) ≤ n ≡ tt
    u'' = cong-pred (λ x → x ≤ n ≡ tt) (+suc (a + b) (c + d)) u'
    sum<n : (a + b) + (c + d) < n ≡ tt
    sum<n = suc≤< {n = (a + b) + (c + d)} {n' = n} u''
    step1 : b + d ≤ (a + b) + d ≡ tt
    step1 = ≤+mono1 {x = b} {x' = a + b} {y = d} (≤+2 a b)
    step2 : (a + b) + d ≤ (a + b) + (c + d) ≡ tt
    step2 = ≤+mono2 {x = a + b} {y = d} {y' = c + d} (≤+2 c d)
    bd≤sum : b + d ≤ (a + b) + (c + d) ≡ tt
    bd≤sum = ≤-trans {x = b + d} {y = (a + b) + d} {z = (a + b) + (c + d)} step1 step2

trans! : ∀ {n : ℕ}{A B C : Tp!} →
         (d : A <:! B) →
         (d' : B <:! C) →
         size d + size d' ≤ n ≡ tt →
         A <:! C
-- Atomic case.
trans!
  (Nat<! {b = b₁} {b' = b₂} ok₁)
  (Nat<! {b = .b₂} {b' = b₃} ok₂) _ =
  Nat<! (layerOK-trans b₁ b₂ b₃ ok₁ ok₂)

-- Ordinary followed by ordinary.
trans!{suc n}
  (Fun<! {q = ff}
         {b = b₁} {b' = b₂}
         {A = A₁} {B = B₁}
         {A' = A₂} {B' = B₂}
         ok₁ dom₁ cod₁)
  (Fun<! {q = ff}
         {b = .b₂} {b' = b₃}
         {A = .A₂} {B = .B₂}
         {A' = A₃} {B' = B₃}
         ok₂ dom₂ cod₂)
  u =
  Fun<! {q = ff}
        {b = b₁} {b' = b₃}
        {A = A₁} {B = B₁}
        {A' = A₃} {B' = B₃}
        (layerOK-trans b₁ b₂ b₃ ok₁ ok₂)
        (trans!{n} dom₂ dom₁ (trans-fuel-dom (size dom₁) (size cod₁) (size dom₂) (size cod₂) u))
        (trans!{n} cod₁ cod₂ (trans-fuel-cod (size dom₁) (size cod₁) (size dom₂) (size cod₂) u))

-- Ordinary followed by Seq-shaped.
trans!{suc n}
  (Fun<! {q = ff} ok₁ dom₁ cod₁)
  (Fun<! {q = tt} ok₂ dom₂ cod₂)
  u =
  Fun<! {q = tt}
    refl
    (trans!{n} dom₂ (cov! dom₁) helper-dom)
    (trans!{n} (cov! cod₁) cod₂ helper-cod)
  where
    helper-dom : size dom₂ + size (cov! dom₁) ≤ n ≡ tt
    helper-dom rewrite size-cov! dom₁ =
      trans-fuel-dom (size dom₁) (size cod₁) (size dom₂) (size cod₂) u
    helper-cod : size (cov! cod₁) + size cod₂ ≤ n ≡ tt
    helper-cod rewrite size-cov! cod₁ =
      trans-fuel-cod (size dom₁) (size cod₁) (size dom₂) (size cod₂) u

-- Seq-shaped followed by ordinary.
trans!{suc n}
  (Fun<! {q = tt} ok₁ dom₁ cod₁)
  (Fun<! {q = ff} ok₂ dom₂ cod₂)
  u =
  Fun<! {q = tt}
    refl
    (trans!{n} dom₂ dom₁ (trans-fuel-dom (size dom₁) (size cod₁) (size dom₂) (size cod₂) u))
    (trans!{n} cod₁ cod₂ (trans-fuel-cod (size dom₁) (size cod₁) (size dom₂) (size cod₂) u))

-- Seq-shaped followed by Seq-shaped.
trans!{suc n}
  (Fun<! {q = tt} ok₁ dom₁ cod₁)
  (Fun<! {q = tt} ok₂ dom₂ cod₂)
  u =
  Fun<! {q = tt}
    refl
    (trans!{n} dom₂ (↑-pull-dom dom₁) helper-dom)
    (trans!{n} (↑-pull-codom cod₁) cod₂ helper-cod)
  where
    helper-dom : size dom₂ + size (↑-pull-dom dom₁) ≤ n ≡ tt
    helper-dom rewrite size-↑-pull-dom dom₁ =
      trans-fuel-dom (size dom₁) (size cod₁) (size dom₂) (size cod₂) u
    helper-cod : size (↑-pull-codom cod₁) + size cod₂ ≤ n ≡ tt
    helper-cod rewrite size-↑-pull-codom cod₁ =
      trans-fuel-cod (size dom₁) (size cod₁) (size dom₂) (size cod₂) u
