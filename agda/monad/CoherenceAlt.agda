module CoherenceAlt where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics
open import Spec
open import Uniqueness
-- open import Completeness (commented out because no interaction points)
-- open import Soundness

soundness : ∀ {T T' : Tp!} →
         T < Nothing :! T' →
         ⟦ T ⟧ <: ⟦ T' ⟧
soundness d = {!!}

-- Soundness at the level of source types
soundness' : ∀ {A B : Tp} → ⌈ A ⌉ < Nothing :! ⌈ B ⌉ → A <: B
soundness' {A} {B} d = Trans (raw<norm A) (Trans (soundness d) (norm<raw B))

completeness : ∀ {A B : Tp} →
               A <: B →
               ⌈ A ⌉ < Nothing :! ⌈ B ⌉
completeness d = {!!}

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

-- How can I put this directly in the coherence proof?
-- I frequently find myself wanting to use 'rewrite' mid-proof
≃-eq : ∀ {A B : Tp} {d d' : A <: B} → d ≡ d' → d ≃ d'
≃-eq eq rewrite eq = ≃-refl _

round-trip : ∀ {A B : Tp} (d : A <: B) → d ≃ soundness' (completeness d)
round-trip d = {!!}

helper : ∀ {A B : Tp} (d d' : A <: B) → completeness d ≡ completeness d'
helper d d' = uniqueness (completeness d) (completeness d')

coherence : ∀ {A B : Tp} (d d' : A <: B) → d ≃ d'
coherence d d' = 
  ≃-trans (round-trip d)
    (≃-trans (≃-eq (cong soundness' (helper d d'))) (≃-sym (round-trip d')))
