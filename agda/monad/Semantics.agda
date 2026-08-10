module Semantics where

open import lib
open import Tp
open import Declarative

-- Interpret a normalized type as a source type.
infix 100 ⟦_⟧
⟦_⟧ : Tp! → Tp
⟦ ff !N ⟧       = N
⟦ tt !N ⟧       = L N
⟦ ff ! A ⇒ B ⟧  = ⟦ A ⟧ ⇒ ⟦ B ⟧
⟦ tt ! A ⇒ B ⟧  = L (⟦ A ⟧ ⇒ ⟦ B ⟧)

-- Normalize a source type.
infix 100 ⌈_⌉
⌈_⌉ : Tp → Tp!
⌈ N ⌉      = ff !N
⌈ L T ⌉    = ↑ ⌈ T ⌉
⌈ T ⇒ T' ⌉ = ff ! ⌈ T ⌉ ⇒ ⌈ T' ⌉

_≺_ : Tp! → Tp → Set
T ≺ T' =   ⌈ T' ⌉ ≡ T

↑<L⟦⟧ : ∀ (A : Tp!) → ⟦ ↑ A ⟧ <: L ⟦ A ⟧
↑<L⟦⟧ (ff !N)      = refl-raw
↑<L⟦⟧ (tt !N)      = Pure
↑<L⟦⟧ (ff ! A ⇒ B) = refl-raw
↑<L⟦⟧ (tt ! A ⇒ B) = Pure

L⟦⟧<↑ : ∀ (A : Tp!) → L ⟦ A ⟧ <: ⟦ ↑ A ⟧
L⟦⟧<↑ (ff !N)      = refl-raw
L⟦⟧<↑ (tt !N)      = Join
L⟦⟧<↑ (ff ! A ⇒ B) = refl-raw
L⟦⟧<↑ (tt ! A ⇒ B) = Join

-- A source type is equivalent to the interpretation of its normalization.
mutual
  raw<norm : ∀ (T : Tp) → T <: ⟦ ⌈ T ⌉ ⟧
  raw<norm N       = NatRefl
  raw<norm (L T)   = Trans (Cov (raw<norm T)) (L⟦⟧<↑ ⌈ T ⌉)
  raw<norm (T ⇒ U) = Fun (norm<raw T) (raw<norm U)

  norm<raw : ∀ (T : Tp) → ⟦ ⌈ T ⌉ ⟧ <: T
  norm<raw N       = NatRefl
  norm<raw (L T)   = Trans (↑<L⟦⟧ ⌈ T ⌉) (Cov (norm<raw T))
  norm<raw (T ⇒ U) = Fun (raw<norm T) (norm<raw U)

norm-norm : ∀ {T : Tp!} → ⌈ ⟦ T ⟧ ⌉ ≡ T
norm-norm {tt !N} = refl
norm-norm {ff !N} = refl
norm-norm {tt ! T ⇒ T₁} rewrite norm-norm {T} | norm-norm {T₁} = refl
norm-norm {ff ! T ⇒ T₁} rewrite norm-norm {T} | norm-norm {T₁} = refl
