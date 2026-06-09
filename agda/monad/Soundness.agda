module Soundness where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics

nat-sound : ∀ {b b' : 𝔹} →
            layerOK b b' ≡ tt →
            ⟦ b !N ⟧ <: ⟦ b' !N ⟧
nat-sound {ff} {ff} refl = refl-raw
nat-sound {ff} {tt} refl = Pure
nat-sound {tt} {tt} refl = refl-raw
nat-sound {tt} {ff} ()

-- Soundness for ordinary function rule (not seq shaped)
funOrd-sound : ∀ {b b' : 𝔹} {A B A' B' : Tp!} →
               layerOK b b' ≡ tt →
               ⟦ A' ⟧ <: ⟦ A ⟧ →
               ⟦ B  ⟧ <: ⟦ B' ⟧ →
               ⟦ b ! A ⇒ B ⟧ <: ⟦ b' ! A' ⇒ B' ⟧
funOrd-sound {ff} {ff} ok dom cod =
  Fun dom cod
funOrd-sound {ff} {tt} ok dom cod =
  Trans (Fun dom cod) Pure
funOrd-sound {tt} {ff} () dom cod
funOrd-sound {tt} {tt} ok dom cod =
  Cov (Fun dom cod)

-- Soundness for Seq-shaped function rule where b, b' = ff
seq-core-sound : ∀ {A B A' B' : Tp!} →
                 ⟦ A' ⟧ <: ⟦ ↑ A ⟧ →
                 ⟦ ↑ B ⟧ <: ⟦ B' ⟧ →
                 L (⟦ A ⟧ ⇒ ⟦ B ⟧) <: ⟦ A' ⟧ ⇒ ⟦ B' ⟧
seq-core-sound {A} {B} dom cod =
  Trans Seq
    (Fun (Trans dom (↑<L⟦⟧ A))
         (Trans (L⟦⟧<↑ B) cod))

-- Soundness for the full Seq-shaped fun rule
funSeq-sound : ∀ {b b' : 𝔹} {A B A' B' : Tp!} →
               ⟦ A' ⟧ <: ⟦ ↑ A ⟧ →
               ⟦ ↑ B ⟧ <: ⟦ B' ⟧ →
               ⟦ b ! A ⇒ B ⟧ <: ⟦ b' ! A' ⇒ B' ⟧
funSeq-sound {ff} {ff} dom cod =
  Trans Pure (seq-core-sound dom cod)
funSeq-sound {ff} {tt} dom cod =
  Trans (Trans Pure (seq-core-sound dom cod)) Pure
funSeq-sound {tt} {ff} dom cod =
  seq-core-sound dom cod
funSeq-sound {tt} {tt} dom cod =
  Trans (seq-core-sound dom cod) Pure

-- Main soundness theorem
sound! : ∀ {A B : Tp!} → A <:! B → ⟦ A ⟧ <: ⟦ B ⟧
sound! (Nat<! ok) =
  nat-sound ok
sound! (Fun<! {q = ff} ok dom cod) =
  funOrd-sound ok (sound! dom) (sound! cod)
sound! (Fun<! {q = tt} ok dom cod) =
  funSeq-sound (sound! dom) (sound! cod)
