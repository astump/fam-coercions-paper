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
N<:Funbot {N} {L B} refl h2 (Trans h3 h4) = {!!}
N<:Funbot {N} {B ⇒ B₁} refl refl (Trans h3 h4) = {!!}
N<:Funbot {L A} {L B} h1 h2 h3 = {!!}
N<:Funbot {L A} {B ⇒ B₁} h1 refl h3 = {!!}

Fun<:Nbot : {A B : Tp} {T' T'' : Tp!} {x x₁ : 𝔹} →
  ⌈ A ⌉ ≡ x ! T' ⇒ T'' → ⌈ B ⌉ ≡ x₁ !N → A <: B
  → ⊥ {lzero}
Fun<:Nbot h1 h2 h3 = {!!}

completeness : ∀{f : Flag}{T T' : Tp!} →
               ⊨ T < f :! T' →
               T < f :! T'
completeness {Left} {tt !N} {tt !N} eq = Nat! triv
completeness {Left} {tt !N} {ff !N} eq
  with eq {L N} {N} refl refl
... | h = ⊥-elim (LN<:Nbot h)
completeness {Left} {ff !N} {tt !N} eq = Nat! triv
completeness {Left} {ff !N} {ff !N} eq
  with eq {L N} {N} refl refl
... | h = ⊥-elim (LN<:Nbot h)
completeness {Left} {tt !N} {tt ! T' ⇒ T''} eq
  with eq {L N} {L (⟦ T' ⟧ ⇒ ⟦ T'' ⟧)} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Left} {tt !N} {ff ! T' ⇒ T''} eq
  with eq {L N} {⟦ T' ⟧ ⇒ ⟦ T'' ⟧} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Left} {ff !N} {tt ! T' ⇒ T''} eq
  with eq {L N} {L (⟦ T' ⟧ ⇒ ⟦ T'' ⟧)} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Left} {ff !N} {ff ! T' ⇒ T''} eq
  with eq {L N} {⟦ T' ⟧ ⇒ ⟦ T'' ⟧} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Left} {tt ! T ⇒ T₁} {tt !N} eq
  with eq {L (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)} {L N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Left} {tt ! T ⇒ T₁} {ff !N} eq
  with eq {L (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)} {N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Left} {ff ! T ⇒ T₁} {tt !N} eq
  with eq {L (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)} {L N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Left} {ff ! T ⇒ T₁} {ff !N} eq
  with eq {L (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)} {N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Right} {tt !N} {tt !N} eq = Nat! triv
completeness {Right} {tt !N} {ff !N} eq = Nat! triv
completeness {Right} {ff !N} {tt !N} eq = Nat! triv
completeness {Right} {ff !N} {ff !N} eq = Nat! triv
completeness {Right} {tt !N} {tt ! T' ⇒ T''} eq
  with eq {L N} {L (⟦ T' ⟧ ⇒ ⟦ T'' ⟧)} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Right} {tt !N} {ff ! T' ⇒ T''} eq
  with eq {L N} {L (⟦ T' ⟧ ⇒ ⟦ T'' ⟧)} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Right} {ff !N} {tt ! T' ⇒ T''} eq
  with eq {N} {L (⟦ T' ⟧ ⇒ ⟦ T'' ⟧)} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Right} {ff !N} {ff ! T' ⇒ T''} eq
  with eq {N} {L (⟦ T' ⟧ ⇒ ⟦ T'' ⟧)} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Right} {tt ! T ⇒ T₁} {tt !N} eq
  with eq {L (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)} {L N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Right} {tt ! T ⇒ T₁} {ff !N} eq
  with eq {L (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)} {L N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Right} {ff ! T ⇒ T₁} {tt !N} eq
  with eq {⟦ T ⟧ ⇒ ⟦ T₁ ⟧} {L N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Right} {ff ! T ⇒ T₁} {ff !N} eq
  with eq {⟦ T ⟧ ⇒ ⟦ T₁ ⟧} {L N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Nothing} {tt !N} {tt !N} eq = Nat! triv
completeness {Nothing} {tt !N} {ff !N} eq
  with eq {L N} {N} refl refl
... | h = ⊥-elim (LN<:Nbot h)
completeness {Nothing} {ff !N} {tt !N} eq = Nat! triv
completeness {Nothing} {ff !N} {ff !N} eq = Nat! triv
completeness {Nothing} {tt !N} {tt ! T' ⇒ T''} eq
  with eq {L N} {L (⟦ T' ⟧ ⇒ ⟦ T'' ⟧)} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Nothing} {tt !N} {ff ! T' ⇒ T''} eq
  with eq {L N} {⟦ T' ⟧ ⇒ ⟦ T'' ⟧} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Nothing} {ff !N} {tt ! T' ⇒ T''} eq
  with eq {N} {L (⟦ T' ⟧ ⇒ ⟦ T'' ⟧)} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Nothing} {ff !N} {ff ! T' ⇒ T''} eq
  with eq {N} {⟦ T' ⟧ ⇒ ⟦ T'' ⟧} refl (norm-norm)
... | h = ⊥-elim (N<:Funbot refl refl h)
completeness {Nothing} {tt ! T ⇒ T₁} {tt !N} eq
  with eq {L (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)} {L N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Nothing} {tt ! T ⇒ T₁} {ff !N} eq
  with eq {L (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)} {N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Nothing} {ff ! T ⇒ T₁} {tt !N} eq
  with eq {⟦ T ⟧ ⇒ ⟦ T₁ ⟧} {L N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)
completeness {Nothing} {ff ! T ⇒ T₁} {ff !N} eq
  with eq {⟦ T ⟧ ⇒ ⟦ T₁ ⟧} {N} norm-norm refl
... | h = ⊥-elim (Fun<:Nbot refl refl h)

completeness {Left} {x ! T ⇒ T₁} {x₁ ! T' ⇒ T''} eq = {!!}
completeness {Right} {x ! T ⇒ T₁} {x₁ ! T' ⇒ T''} eq = {!!}
completeness {Nothing} {tt ! T ⇒ T₁} {tt ! T' ⇒ T''} eq
  with eq {L (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)} {L (⟦ T' ⟧ ⇒ ⟦ T'' ⟧)} norm-norm norm-norm
... | Cov (Fun h h₁) = Fun! {j = Ord} triv {!!} {!!}
... | Cov (Trans h h₁) = {!!}
... | Trans h h₁ = {!!}
completeness {Nothing} {tt ! T ⇒ T₁} {ff ! T' ⇒ T''} eq = {!!}
completeness {Nothing} {ff ! T ⇒ T₁} {tt ! T' ⇒ T''} eq = {!!}
completeness {Nothing} {ff ! T ⇒ T₁} {ff ! T' ⇒ T''} eq
  with eq {⟦ T ⟧ ⇒ ⟦ T₁ ⟧} {⟦ T' ⟧ ⇒ ⟦ T'' ⟧} norm-norm norm-norm
... | Fun h h₁ = Fun! {j = Ord} triv
  (completeness λ {A} {B} h1 h2 →
  Trans (raw<norm A) (Trans (Trans
  (<:OfEq (cong (λ x → ⟦ x ⟧) h1)) (
  Trans h (<:OfEq (cong (λ x → ⟦ x ⟧) (sym h2))))) (norm<raw B)))
  (completeness λ {A} {B} h1 h2 →
  Trans (raw<norm A) (Trans (Trans
  (<:OfEq (cong (λ x → ⟦ x ⟧) h1)) (
  Trans h₁ (<:OfEq (cong (λ x → ⟦ x ⟧) (sym h2))))) (norm<raw B)))
... | Trans h h₁ = Fun! {!!} {!!} {!!}
{-
completeness λ {A} {B} h1 h2 →
  Trans (raw<norm A) (Trans
  (<:OfEq (cong (λ x → ⟦ x ⟧) h1)) (
  Trans (Trans (Trans h h₁) (
  <:OfEq (cong (λ x → ⟦ x ⟧) (sym h2)))) (norm<raw B)))
  -}
