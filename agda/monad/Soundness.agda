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

↑neqffFun : {T T' T'' : Tp!} → ↑ T ≡ ff ! T' ⇒ T'' → ⊥ {lzero}
↑neqffFun {x !N} ()
↑neqffFun {x ! T ⇒ T₁} ()

eqOfNormff : {A : Tp} → {T T' : Tp!} →
    ⌈ A ⌉ ≡ ff ! T ⇒ T' →
    ∃ Tp (λ B → ∃ Tp (λ B' →
      A ≡ B ⇒ B' ∧
      ⌈ B  ⌉ ≡ T ∧
      ⌈ B' ⌉ ≡ T' ))
eqOfNormff {L A} ex = ⊥-elim (↑neqffFun ex)
eqOfNormff {A ⇒ A₁} refl = A , A₁ , refl , refl , refl

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
soundness {Right} (Fun! {j = Ord} x eq eq₁) {A} {B} eqA eqB = {!!}
soundness {Right} (Fun! {j = Seq} x eq eq₁) {A} {B} eqA eqB = {!!}

soundness {Nothing} (Nat! {ff} {b' = tt} x) {N} {L B} eqA eqB =
  natChain {L B} (trans (↑idem ⌈ B ⌉) eqB)
soundness {Nothing} (Nat! {tt} {b' = tt} x) {L A} {L B} eqA eqB = 
  Trans (collapseL eqA) (expandL eqB)
soundness {Nothing} (Nat! {ff} {b' = tt} x) {L A} {L B} eqA eqB = ⊥-elim (↑neqff eqA)
soundness {Nothing} (Nat! {ff} {b' = ff} x) {N} {N} eqA eqB = NatRefl
soundness {Nothing} (Nat! {ff} {b' = ff} x) {N} {L B} eqA eqB = ⊥-elim (↑neqff eqB)
soundness {Nothing} (Nat! {ff} {b' = ff} x) {L A} {N} eqA eqB = ⊥-elim (↑neqff eqA)
soundness {Nothing} (Nat! {ff} {b' = ff} x) {L A} {L B} eqA eqB = ⊥-elim (↑neqff eqA)

soundness {Nothing} (Fun! {tt} {tt} {j = Ord} x eq eq₁) {A} {B} eqA eqB = Trans
  (raw<norm A)
  (Trans (Trans (<:OfEq (cong (λ x → ⟦ x ⟧) eqA)) (
  Trans (Cov (Fun
    ((soundness eq) norm-norm norm-norm) (
    (soundness eq₁) norm-norm norm-norm )))
  (<:OfEq (cong (λ x → ⟦ x ⟧) (sym eqB)))))
  (norm<raw B))
soundness {Nothing} (Fun! {ff} {tt} {j = Ord} x eq eq₁) eqA eqB = {!!}
soundness {Nothing} (Fun! {ff} {ff} {j = Ord} x eq eq₁) {A} {B} eqA eqB
    with eqOfNormff {A} eqA
... | A₂ , (B₂ , (hA , hA₂ , hB₂))
    with eqOfNormff {B} eqB
... | A₂' , (B₂' , (hB , hA₂' , hB₂'))
    rewrite hA | hB = Fun ((soundness eq) hA₂' hA₂) ((soundness eq₁) hB₂ hB₂')

soundness {Nothing} (Fun! {j = Seq} x eq eq₁) eqA eqB = {!!}
