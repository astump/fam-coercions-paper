-- {-# OPTIONS --allow-unsolved-metas #-}

module Soundness where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics
open import Spec

↑idem : (T : Tp!) → ↑ ( ↑ T) ≡ ↑ T
↑idem (x !N) = refl
↑idem (x ! T ⇒ T₁) = refl

natChain : {A : Tp} → ↑ ⌈ A ⌉ ≡ tt !N → N <: A
natChain {N} eq = NatRefl
natChain {L A} eq rewrite ↑idem ⌈ A ⌉ = Trans Pure (Cov (natChain {A} eq))

collapseL : {A : Tp} → ↑ ⌈ A ⌉ ≡ tt !N → L A <: L N
collapseL {N} eqA = refl-raw
collapseL {L A} eqA = Trans Join (collapseL {A} (trans (sym (↑idem ⌈ A ⌉)) eqA))

expandL : {B : Tp} → ↑ ⌈ B ⌉ ≡ tt !N → L N <: L B
expandL {N} eqA = refl-raw
expandL {L A} eqA = Trans (expandL {A} (trans (sym (↑idem ⌈ A ⌉)) eqA)) Pure

↑neqff : {T : Tp!} → ↑ T ≡ ff !N → ⊥ {lzero}
↑neqff {x !N} ()
↑neqff {x ! T ⇒ T₁} ()

soundness : ∀{f : Flag}{T T' : Tp!} →
            T < f :! T' →
            ⊨ T < f :! T'
soundness {Left} (Nat! {tt} {tt} x) {L A} {L B} eqA eqB = 
  Trans (collapseL eqA) (expandL eqB)
soundness {Left} (Nat! {ff} {tt} x) {L A} {L B} eqA eqB = 
  Trans (collapseL eqA) (expandL eqB)
soundness {Left} (Fun! x eq eq₁) eqA eqB = {!!}

soundness {Right} (Nat! {ff} {tt} x) {N} {L B} eqA eqB = 
  natChain {L B} (trans (↑idem ⌈ B ⌉) eqB)
soundness {Right} (Nat! {ff} {ff} x) {N} {L B} eqA eqB =
  natChain {L B} (trans (↑idem ⌈ B ⌉) eqB)
soundness {Right} (Nat! {tt} {tt} x) {L A} {L B} eqA eqB =
  Trans (collapseL eqA) (expandL eqB)
soundness {Right} (Nat! {tt} {ff} x) {L A} {L B} eqA eqB =
  Trans (collapseL eqA) (expandL eqB)
soundness {Right} (Nat! {ff} {tt} x) {L A} {L B} eqA eqB = ⊥-elim (↑neqff eqA)
soundness {Right} (Nat! {ff} {ff} x) {L A} {L B} eqA eqB = ⊥-elim (↑neqff eqA)
soundness {Right} (Fun! x eq eq₁) eqA eqB = {!!}

soundness {Nothing} (Nat! {ff} {b' = tt} x) {N} {L B} eqA eqB =
  natChain {L B} (trans (↑idem ⌈ B ⌉) eqB)
soundness {Nothing} (Nat! {tt} {b' = tt} x) {L A} {L B} eqA eqB = 
  Trans (collapseL eqA) (expandL eqB)
soundness {Nothing} (Nat! {ff} {b' = tt} x) {L A} {L B} eqA eqB = ⊥-elim (↑neqff eqA)
soundness {Nothing} (Nat! {ff} {b' = ff} x) {N} {N} eqA eqB = NatRefl
soundness {Nothing} (Nat! {ff} {b' = ff} x) {N} {L B} eqA eqB = ⊥-elim (↑neqff eqB)
soundness {Nothing} (Nat! {ff} {b' = ff} x) {L A} {N} eqA eqB = ⊥-elim (↑neqff eqA)
soundness {Nothing} (Nat! {ff} {b' = ff} x) {L A} {L B} eqA eqB = ⊥-elim (↑neqff eqA)

soundness {Nothing} (Fun! x eq eq₁) eqA eqB = {!!}
