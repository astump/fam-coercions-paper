module Decproc where

open import lib
open import Tp

-- ∀ α : Tp!, b₁ α <:! b₂ α   unless b₁ = tt and b₂ = ff (by pure/join)
layerOK : 𝔹 → 𝔹 → 𝔹
layerOK tt ff = ff
layerOK _  _  = tt

layerOK-tt : ∀ {b : 𝔹} → layerOK b tt ≡ tt
layerOK-tt {ff} = refl
layerOK-tt {tt} = refl

-- Used in the statement of pure-funOrd in Coherence.agda
layerOK-relax : ∀ {b₀ b' : 𝔹} → layerOK tt b' ≡ tt → layerOK b₀ b' ≡ tt
layerOK-relax {b₀} {tt} ok = layerOK-tt {b₀}
layerOK-relax {b₀} {ff} ()

-- The algorithmic coersion relation on normalized types
infix 5 _<:!_
data _<:!_ : Tp! → Tp! → Set where
  Nat! : ∀ {b b' : 𝔹} →
          layerOK b b' ≡ tt →
          (b !N) <:! (b' !N)

  -- Ordinary function rule (contravariant domain, covariant codomain)
  FunOrd! : ∀ {b b' : 𝔹} {A B A' B' : Tp!} →
           layerOK b b' ≡ tt →
           A' <:! A →
           B  <:! B' →
           (b ! A ⇒ B) <:! (b' ! A' ⇒ B')

  -- Sequenced function rule (internalizes the Seq law)
  -- Does not require layerOK
  FunSeq! : ∀ {b b' : 𝔹} {A B A' B' : Tp!} →
           A'  <:! ↑ A →
           ↑ B <:! B' →
           (b ! A ⇒ B) <:! (b' ! A' ⇒ B')

-- Reflexivity is admissible.
refl! : ∀ {A : Tp!} → A <:! A
refl! {ff !N}      = Nat! refl
refl! {tt !N}      = Nat! refl
refl! {ff ! A ⇒ B} = FunOrd! refl refl! refl!
refl! {tt ! A ⇒ B} = FunOrd! refl refl! refl!
