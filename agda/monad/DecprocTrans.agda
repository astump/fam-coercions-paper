module DecprocTrans where

open import lib
open import Tp
open import Decproc

-- Number of arrow rules in a derivation, used as the fuel measure
size : ∀ {A B : Tp!} → A <:! B → ℕ
size (Nat! _)        = 0
size (FunOrd! _ d e) = suc (size d) + size e
size (FunSeq! d e)   = suc (size d) + size e

-- Completeness for the coveriance rule
cov! : ∀ {A B : Tp!} → A <:! B → ↑ A <:! ↑ B
cov! (Nat! _)            = Nat! refl
cov! (FunOrd! _ dom cod) = FunOrd! refl dom cod
cov! (FunSeq! dom cod)   = FunSeq! dom cod

-- cov! preserves size.
size-cov! : ∀ {A B : Tp!} (d : A <:! B) → size (cov! d) ≡ size d
size-cov! (Nat! _)        = refl
size-cov! (FunOrd! _ _ _) = refl
size-cov! (FunSeq! _ _)   = refl

↑-pull-dom : ∀ {A' A : Tp!} →
             A'   <:! ↑ A →
             ↑ A' <:! ↑ A
↑-pull-dom {b !N} {b' !N} (Nat! _) = Nat! refl
↑-pull-dom {b ! A' ⇒ B'} {b' ! A ⇒ B} (FunOrd! _ d e) = FunOrd! refl d e
↑-pull-dom {b ! A' ⇒ B'} {b' ! A ⇒ B} (FunSeq! d e)   = FunSeq! d e

-- ↑-pull-dom preserves size.
size-↑-pull-dom : ∀ {A' A : Tp!} (d : A' <:! ↑ A) → size (↑-pull-dom d) ≡ size d
size-↑-pull-dom {b !N} {b' !N} (Nat! _) = refl
size-↑-pull-dom {b ! A' ⇒ B'} {b' ! A ⇒ B} (FunOrd! _ _ _) = refl
size-↑-pull-dom {b ! A' ⇒ B'} {b' ! A ⇒ B} (FunSeq! _ _)   = refl

↑-pull-codom : ∀ {A' A : Tp!} →
               ↑ A <:! A' →
               ↑ A <:! ↑ A'
↑-pull-codom {b !N} {b' !N} (Nat! _) = Nat! refl
↑-pull-codom {b ! A' ⇒ B'} {b' ! A ⇒ B} (FunOrd! _ d e) = FunOrd! refl d e
↑-pull-codom {b ! A' ⇒ B'} {b' ! A ⇒ B} (FunSeq! d e)   = FunSeq! d e

-- ↑-pull-codom preserves size.
size-↑-pull-codom : ∀ {A' A : Tp!} (d : ↑ A <:! A') → size (↑-pull-codom d) ≡ size d
size-↑-pull-codom {b !N} {b' !N} (Nat! _) = refl
size-↑-pull-codom {b ! A' ⇒ B'} {b' ! A ⇒ B} (FunOrd! _ _ _) = refl
size-↑-pull-codom {b ! A' ⇒ B'} {b' ! A ⇒ B} (FunSeq! _ _)   = refl

-- Transitivity of the layer condition
layerOK-trans : ∀ (b₁ b₂ b₃ : 𝔹) →
                layerOK b₁ b₂ ≡ tt →
                layerOK b₂ b₃ ≡ tt →
                layerOK b₁ b₃ ≡ tt
layerOK-trans ff b₂ b₃ p q = refl
layerOK-trans tt ff b₃ ()
layerOK-trans tt tt ff p ()
layerOK-trans tt tt tt p q = refl

-- Fuel bookkeeping: AI-generated
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

-- Fuel bookkeeping: AI-generated
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

-- Completeness for Trans
trans! : ∀ {n : ℕ} {A B C : Tp!} →
         (d  : A <:! B) →
         (d' : B <:! C) →
         size d + size d' ≤ n ≡ tt →
         A <:! C

-- Base ∘ base
trans!
  (Nat! {b = b₁} {b' = b₂} ok₁)
  (Nat! {b = .b₂} {b' = b₃} ok₂) _ =
  Nat! (layerOK-trans b₁ b₂ b₃ ok₁ ok₂)

-- Ordinary ∘ ordinary
trans! {suc n}
  (FunOrd! {b = b₁} {b' = b₂} {A = A₁} {B = B₁} {A' = A₂} {B' = B₂}
          ok₁ dom₁ cod₁)
  (FunOrd! {b = .b₂} {b' = b₃} {A = .A₂} {B = .B₂} {A' = A₃} {B' = B₃}
          ok₂ dom₂ cod₂)
  fuel =
  FunOrd! {b = b₁} {b' = b₃} {A = A₁} {B = B₁} {A' = A₃} {B' = B₃}
         (layerOK-trans b₁ b₂ b₃ ok₁ ok₂)
         (trans! {n} dom₂ dom₁
                 (trans-fuel-dom (size dom₁) (size cod₁) (size dom₂) (size cod₂) fuel))
         (trans! {n} cod₁ cod₂
                 (trans-fuel-cod (size dom₁) (size cod₁) (size dom₂) (size cod₂) fuel))

-- Ordinary ∘ sequenced
trans! {suc n}
  (FunOrd! ok₁ dom₁ cod₁)
  (FunSeq! dom₂ cod₂)
  fuel =
  FunSeq! (trans! {n} dom₂ (cov! dom₁) helper-dom)
         (trans! {n} (cov! cod₁) cod₂ helper-cod)
  where
    helper-dom : size dom₂ + size (cov! dom₁) ≤ n ≡ tt
    helper-dom rewrite size-cov! dom₁ =
      trans-fuel-dom (size dom₁) (size cod₁) (size dom₂) (size cod₂) fuel
    helper-cod : size (cov! cod₁) + size cod₂ ≤ n ≡ tt
    helper-cod rewrite size-cov! cod₁ =
      trans-fuel-cod (size dom₁) (size cod₁) (size dom₂) (size cod₂) fuel

-- Sequenced ∘ ordinary
trans! {suc n}
  (FunSeq! dom₁ cod₁)
  (FunOrd! ok₂ dom₂ cod₂)
  fuel =
  FunSeq! (trans! {n} dom₂ dom₁
                 (trans-fuel-dom (size dom₁) (size cod₁) (size dom₂) (size cod₂) fuel))
         (trans! {n} cod₁ cod₂
                 (trans-fuel-cod (size dom₁) (size cod₁) (size dom₂) (size cod₂) fuel))

-- Sequenced ∘ sequenced
trans! {suc n}
  (FunSeq! dom₁ cod₁)
  (FunSeq! dom₂ cod₂)
  fuel =
  FunSeq! (trans! {n} dom₂ (↑-pull-dom dom₁) helper-dom)
         (trans! {n} (↑-pull-codom cod₁) cod₂ helper-cod)
  where
    helper-dom : size dom₂ + size (↑-pull-dom dom₁) ≤ n ≡ tt
    helper-dom rewrite size-↑-pull-dom dom₁ =
      trans-fuel-dom (size dom₁) (size cod₁) (size dom₂) (size cod₂) fuel
    helper-cod : size (↑-pull-codom cod₁) + size cod₂ ≤ n ≡ tt
    helper-cod rewrite size-↑-pull-codom cod₁ =
      trans-fuel-cod (size dom₁) (size cod₁) (size dom₂) (size cod₂) fuel
