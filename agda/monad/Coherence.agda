module Coherence where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics
open import Spec
open import Uniqueness
open import Completeness
open import Soundness


spec→decl : ∀ {A B : Tp} →
            ⊨ ⌈ A ⌉ < Nothing :! ⌈ B ⌉ →
            A <: B
spec→decl d = {!!}

decl→spec : ∀ {A B : Tp} →
            A <: B →
            ⊨ ⌈ A ⌉ < Nothing :! ⌈ B ⌉
decl→spec d = {!!}

-- Is this provable as ≡? should it be changed to ≃ ?
spec-decl-id : ∀ {A B : Tp} (d : A <: B) →
  spec→decl (decl→spec d) ≡ d
spec-decl-id d = {!!}

-- Is this provable as ≡? should it be changed to ≃ ?
spec-sound-complete-id : ∀ {A B : Tp} (p : ⊨ ⌈ A ⌉ < Nothing :! ⌈ B ⌉) →
  spec→decl {A} {B}
    (soundness {Nothing} {⌈ A ⌉} {⌈ B ⌉}
      (completeness {Nothing} {⌈ A ⌉} {⌈ B ⌉} p))
  ≡ spec→decl {A} {B} p
spec-sound-complete-id p = {!!}

-- Equivalence of declarative coersions, modulo the monad laws
infix 4 _≃_
data _≃_ : {A B : Tp} → A <: B → A <: B → Set where
  ≃-refl  : ∀ {A B} (d : A <: B) → d ≃ d

  ≃-sym   : ∀ {A B} {d₁ d₂ : A <: B}
            → d₁ ≃ d₂
            → d₂ ≃ d₁

  ≃-trans : ∀ {A B} {d₁ d₂ d₃ : A <: B}
            → d₁ ≃ d₂ → d₂ ≃ d₃
            → d₁ ≃ d₃

≃-eq : ∀ {A B : Tp} {d d' : A <: B} → d ≡ d' → d ≃ d'
≃-eq eq rewrite eq = ≃-refl _

round-trip : ∀ {A B : Tp} (d : A <: B) →
  d ≃ spec→decl (soundness (completeness {Nothing} (decl→spec d)))
round-trip {A} {B} d
  rewrite spec-sound-complete-id {A} {B} (decl→spec {A} {B} d)
        | spec-decl-id {A} {B} d
  = ≃-refl d

helper : ∀ {A B : Tp} (d d' : A <: B) →
         completeness {Nothing} (decl→spec d) ≡ completeness {Nothing} (decl→spec d')
helper d d' = uniqueness (
  completeness {Nothing} (decl→spec d)) (
  completeness {Nothing} (decl→spec d'))

sound∘complete→decl : ∀ {A B : Tp} →
  ⌈ A ⌉ < Nothing :! ⌈ B ⌉ →
  A <: B
sound∘complete→decl {A} {B} x =
  spec→decl {A} {B} (soundness {Nothing} {⌈ A ⌉} {⌈ B ⌉} x)

coherence : ∀ {A B : Tp} (d d' : A <: B) → d ≃ d'
coherence d d' = ≃-trans (round-trip d) (
  ≃-trans (≃-eq (cong sound∘complete→decl (helper d d'))) (≃-sym (round-trip d')) )
