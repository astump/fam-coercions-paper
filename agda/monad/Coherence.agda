module Coherence where

open import lib
open import Tp
open import Declarative
open import Decproc
open import DecprocTrans
open import Semantics
open import Completeness
open import Soundness

-- Equivalence of declarative coercions modulo monad laws
--
-- Two derivations d₁ d₂ : A <: B are equivalent, written d₁ ≃ d₂, if they
-- are equal up to the laws of a monad (which laws?)
--
-- See fmap/Decl.agda
-- Do these need to be justified somehow?
--

infix 4 _≃_

data _≃_ : {A B : Tp} → A <: B → A <: B → Set where

  -- Equivalence relation rules
  --
  ≃-refl  : ∀ {A B} (d : A <: B) → d ≃ d

  ≃-sym   : ∀ {A B} {d₁ d₂ : A <: B}
            → d₁ ≃ d₂
            → d₂ ≃ d₁

  ≃-trans : ∀ {A B} {d₁ d₂ d₃ : A <: B}
            → d₁ ≃ d₂ → d₂ ≃ d₃
            → d₁ ≃ d₃

  -- Congruence for each constructor that has sub-derivations as arguments

  ≃-cong-Fun   : ∀ {T1 T2 T1' T2'}
                 {d₁ d₁' : T1' <: T1} {d₂ d₂' : T2 <: T2'}
                 → d₁ ≃ d₁' → d₂ ≃ d₂'
                 → Fun d₁ d₂ ≃ Fun d₁' d₂'

  ≃-cong-Cov   : ∀ {A B} {d₁ d₂ : A <: B}
                 → d₁ ≃ d₂
                 → Cov d₁ ≃ Cov d₂

  ≃-cong-Trans : ∀ {A B C}
                 {d₁ d₁' : A <: B} {d₂ d₂' : B <: C}
                 → d₁ ≃ d₁' → d₂ ≃ d₂'
                 → Trans d₁ d₂ ≃ Trans d₁' d₂'

  -- Monad Laws (what laws exactly?)

  -- Left identity:
  -- return a >>= h = h a
  --
  -- is this join (Pure a) = a
  ≃-monad-unit-l : ∀ {A} → {!!}

  -- Right identity:
  -- m >>= return = m 
  ≃-monad-unit-r : ∀ {A} → {!!}

  -- Associativity:
  -- (m >>= g) >>= h = m >>= (λ x → g x >>= h)
  ≃-monad-assoc  : ∀ {A} → {!!}

  -- TODO : Add category and functor laws

-- Uniqueness:
--
-- Any two proofs of A <:! B are propositionally equal.  
-- How do we handle the implicit q : 𝔹 in Fun<!:? 
-- Is q uniquely determined by the other parameters? 

--   q = tt is required when funOK ff b b' = ff
--   q = ff is valid whenever funOK ff b b' = tt

unique! : ∀ {A B : Tp!} (d₁ d₂ : A <:! B) → d₁ ≡ d₂
unique! d₁ d₂ = {!!}

-- Alternative (easier?)
unique!' : ∀ {A B : Tp!} (d₁ d₂ : A <:! B) → sound! d₁ ≡ sound! d₂
unique!' d₁ d₂ = {!!}

-- Round-trip equivalence
-- 
-- Running a declarative derivation through completeness then through soundness
-- gives a derivation equivalent to the original.
--
-- See reify-eval in agda/fmap/Fmap.agda.

round-trip : ∀ {A B : Tp} (d : A <: B) → d ≃ sound!' (complete! d)
round-trip d = {!!}


-- Coherence
--
-- Any two declarative derivations of type A <: B are
-- equivalent modulo the monad laws.
--
--   d₁ ≃ sound!' (complete! d₁)     by round-trip
--      = sound!' (complete! d₂)     because unique! gives complete! d₁ ≡ complete! d₂
--   d₂ ≃ sound!' (complete! d₂)     by round-trip
--   Therefore d₁ ≃ d₂ by transitivity of ≃

coherence : ∀ {A B : Tp} (d₁ d₂ : A <: B) → d₁ ≃ d₂
coherence d₁ d₂ = {!!}
