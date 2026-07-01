module Soundness where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics

-- The base rule is sound.
nat-sound : ∀ {b b' : 𝔹} →
            layerOK b b' ≡ tt →
            ⟦ b !N ⟧ <: ⟦ b' !N ⟧
nat-sound {ff} {ff} refl = refl-raw
nat-sound {ff} {tt} refl = Pure
nat-sound {tt} {tt} refl = refl-raw
nat-sound {tt} {ff} ()

-- The ordinary function rule is sound.
funOrd-sound : ∀ {b b' : 𝔹} {A B A' B' : Tp!} →
               layerOK b b' ≡ tt →
               ⟦ A' ⟧ <: ⟦ A ⟧ →
               ⟦ B  ⟧ <: ⟦ B' ⟧ →
               ⟦ b ! A ⇒ B ⟧ <: ⟦ b' ! A' ⇒ B' ⟧
funOrd-sound {ff} {ff} ok dom cod = Fun dom cod
funOrd-sound {ff} {tt} ok dom cod = Trans (Fun dom cod) Pure
funOrd-sound {tt} {ff} () dom cod
funOrd-sound {tt} {tt} ok dom cod = Cov (Fun dom cod)

-- Core of the sequenced rule
seq-core-sound : ∀ {A B A' B' : Tp!} →
                 ⟦ A' ⟧ <: ⟦ ↑ A ⟧ →
                 ⟦ ↑ B ⟧ <: ⟦ B' ⟧ →
                 L (⟦ A ⟧ ⇒ ⟦ B ⟧) <: ⟦ A' ⟧ ⇒ ⟦ B' ⟧
seq-core-sound {A} {B} dom cod =
  Trans Seq
    (Fun (Trans dom (↑<L⟦⟧ A))
         (Trans (L⟦⟧<↑ B) cod))

-- The sequenced function rule is sound.
funSeq-sound : ∀ {b b' : 𝔹} {A B A' B' : Tp!} →
               ⟦ A' ⟧ <: ⟦ ↑ A ⟧ →
               ⟦ ↑ B ⟧ <: ⟦ B' ⟧ →
               ⟦ b ! A ⇒ B ⟧ <: ⟦ b' ! A' ⇒ B' ⟧
funSeq-sound {ff} {ff} dom cod = Trans Pure (seq-core-sound dom cod)
funSeq-sound {ff} {tt} dom cod = Trans (Trans Pure (seq-core-sound dom cod)) Pure
funSeq-sound {tt} {ff} dom cod = seq-core-sound dom cod
funSeq-sound {tt} {tt} dom cod = Trans (seq-core-sound dom cod) Pure

-- Main soundness theorem
sound! : ∀ {A B : Tp!} → A <:! B → ⟦ A ⟧ <: ⟦ B ⟧
sound! (Nat! ok)          = nat-sound ok
sound! (FunOrd! ok dom cod) = funOrd-sound ok (sound! dom) (sound! cod)
sound! (FunSeq! dom cod)    = funSeq-sound (sound! dom) (sound! cod)

-- Soundness at the level of source types
sound!' : ∀ {A B : Tp} → ⌈ A ⌉ <:! ⌈ B ⌉ → A <: B
sound!' {A} {B} d = Trans (raw<norm A) (Trans (sound! d) (norm<raw B))
