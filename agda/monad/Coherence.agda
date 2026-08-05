module Coherence where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics
open import Spec
open import Uniqueness
-- open import Completeness (commented out because no interaction points)
-- open import Soundness

-- remove these soundness and completeness defs later
soundness : ∀ {f : Flag} {T T' : Tp!} →
         T < f :! T' →
         ⊨ T < f :! T'
soundness d = {!!}

completeness : ∀ {f : Flag} {T T' : Tp!} →
         ⊨ T < f :! T' →
         T < f :! T'
completeness d = {!!}

spec→decl : ∀ {T T' : Tp!} →
            ⊨ T < Nothing :! T' →
            ⟦ T ⟧ <: ⟦ T' ⟧
spec→decl d = {!!}

decl→spec : ∀ {A B : Tp} →
            A <: B →
            ⊨ ⌈ A ⌉ < Nothing :! ⌈ B ⌉
decl→spec d = {!!}

decl→spec_eq : ∀ {A B : Tp} (d d' : A <: B) →
          decl→spec d ≡ decl→spec d'
decl→spec_eq d d' = {!!}

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

helper : ∀ {A B : Tp} (d d' : A <: B) →
         completeness {Nothing} (decl→spec d) ≡ completeness {Nothing} (decl→spec d')
helper d d' rewrite decl→spec_eq d d' = refl

coherence : ∀ {A B : Tp} (d d' : A <: B) → d ≃ d'
coherence d d' = {!!}
