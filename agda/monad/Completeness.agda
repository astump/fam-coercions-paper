{-# OPTIONS --allow-unsolved-metas #-} -- remove when done

module Completeness where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics
open import Spec

helper : {T : Tp} → T <: N → T ≡ N
helper NatRefl = refl
helper (Trans h h₁) rewrite helper h₁ = helper h

LN<:Nbot : L N <: N → ⊥ {lzero}
LN<:Nbot (Trans d d₁) rewrite helper d₁ = LN<:Nbot d

N<:Funbot : {A B : Tp} {T' T'' : Tp!} {x x₁ : 𝔹} →
  ⌈ A ⌉ ≡ x !N → ⌈ B ⌉ ≡ x₁ ! T' ⇒ T'' → A <: B
  → ⊥ {lzero}
N<:Funbot {N} {L B} refl h2 h3 = {!!}
--N<:Funbot {N} {B} refl {!h2!} {!!}
N<:Funbot {N} {B ⇒ B₁} h h2 h3 = {!!}
N<:Funbot {L A} {L B} h h2 h3 = {!!}
N<:Funbot {L A} {B ⇒ B₁} h h2 h3 = {!!}

completeness : ∀{f : Flag}{T T' : Tp!} →
               ⊨ T < f :! T' →
               T < f :! T'
completeness {Left} eq = {!!}
completeness {Right} eq = {!!}
completeness {Nothing} {tt !N} {tt !N} eq = Nat! triv
-- impossible assumption h.
-- How do i prove that?
completeness {Nothing} {tt !N} {ff !N} eq
  with eq {L N} {N} refl refl
... | h = ⊥-elim (LN<:Nbot h)
completeness {Nothing} {ff !N} {tt !N} eq = Nat! triv
completeness {Nothing} {ff !N} {ff !N} eq = Nat! triv
-- impossible
completeness {Nothing} {x !N} {x₁ ! T' ⇒ T''} eq = {!!}
-- impossible
completeness {Nothing} {x ! T ⇒ T₁} {x₁ !N} eq = {!!}
completeness {Nothing} {tt ! T ⇒ T₁} {tt ! T' ⇒ T''} eq = {!!}
completeness {Nothing} {tt ! T ⇒ T₁} {ff ! T' ⇒ T''} eq = {!!}
completeness {Nothing} {ff ! T ⇒ T₁} {tt ! T' ⇒ T''} eq = {!!}
completeness {Nothing} {ff ! T ⇒ T₁} {ff ! T' ⇒ T''} eq = {!!}
