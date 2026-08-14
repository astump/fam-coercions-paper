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

↑idem : (T : Tp!) → ↑ (↑ T) ≡ ↑ T
↑idem (tt !N) = refl
↑idem (ff !N) = refl
↑idem (x ! T ⇒ T₁) = refl

↑ffBot : {T : Tp!} → ↑ T ≡ ff !N → ⊥ {lzero}
↑ffBot {x !N} ()
↑ffBot {x ! T ⇒ T₁} ()

upNatEq : {A : Tp} → {b : 𝔹} → ⌈ A ⌉ ≡ b !N → ↑ ⌈ A ⌉ ≡ tt !N
upNatEq {N} eq = refl
upNatEq {L A} {tt} eq rewrite ↑idem ⌈ A ⌉ = eq
upNatEq {L A} {ff} eq = ⊥-elim (↑ffBot eq)

funNotNat : {b b' : 𝔹} {X Y : Tp!} → (b ! X ⇒ Y) ≡ b' !N → ⊥ {lzero}
funNotNat ()

upNatEq' : {A : Tp} → {b : 𝔹} → ↑ ⌈ A ⌉ ≡ b !N →
  ∃ 𝔹 λ b → ⌈ A ⌉ ≡ b !N
upNatEq' {N} eq = ff , refl
upNatEq' {L A} {b} eq = b , trans (sym (↑idem ⌈ A ⌉)) eq
upNatEq' {A ⇒ A₁} eq = ⊥-elim (funNotNat eq)

NatClosed : {A B : Tp} → {b : 𝔹} → ⌈ A ⌉ ≡ b !N →
  A <: B → ∃ 𝔹 λ b → ⌈ B ⌉ ≡ b !N
NatClosed h NatRefl = ff , refl
NatClosed {A} h Pure = tt , upNatEq {A} h
NatClosed h (Cov {T1} {T2} le)
  with upNatEq' {T1} h
... | b , eq with NatClosed {T1} {T2} eq le
...   | c , eq2 = tt , upNatEq {T2} eq2
NatClosed {b = b} h (Join {T}) = b , trans (sym (↑idem ⌈ T ⌉)) h
NatClosed h (Fun le le₁) = ⊥-elim (funNotNat h)
NatClosed h (Seq {T1} {T2}) = ⊥-elim (funNotNat h)
NatClosed h (Trans d d₁)
  with NatClosed h d
... | y , hy = NatClosed hy d₁

upFunEq : {A : Tp} {x : 𝔹} {T' T'' : Tp!} →
  ⌈ A ⌉ ≡ x ! T' ⇒ T'' → ↑ ⌈ A ⌉ ≡ tt ! T' ⇒ T''
upFunEq {A} eq rewrite eq = refl

upFunEq' : {A : Tp} {x : 𝔹} {T' T'' : Tp!} → ↑ ⌈ A ⌉ ≡ x ! T' ⇒ T'' →
  ∃ 𝔹 λ b → ∃ Tp! λ U → ∃ Tp! λ V → ⌈ A ⌉ ≡ b ! U ⇒ V
upFunEq' {N} eq = ⊥-elim (funNotNat (sym eq))
upFunEq' {L A} eq = _ , _ , _ , trans (sym (↑idem ⌈ A ⌉)) eq
upFunEq' {A ⇒ A₁} eq = ff , _ , _ , refl

FunClosed : {A B : Tp} {x : 𝔹} {T' T'' : Tp!} → ⌈ A ⌉ ≡ x ! T' ⇒ T'' →
  A <: B → ∃ 𝔹 λ b → ∃ Tp! λ U → ∃ Tp! λ V → ⌈ B ⌉ ≡ b ! U ⇒ V
FunClosed h NatRefl = ⊥-elim (funNotNat (sym h))
FunClosed h (Fun le le₁) = ff , _ , _ , refl
FunClosed h Seq = ff , _ , _ , refl
FunClosed h (Pure {T}) = tt , _ , _ , upFunEq {T} h
FunClosed h (Cov {T1} {T2} le)
  with upFunEq' {T1} h
... | b1 , U1 , V1 , eq1 with FunClosed {T1} {T2} eq1 le
...   | b2 , U2 , V2 , eq2 = tt , _ , _ , upFunEq {T2} eq2
FunClosed h (Join {T}) = _ , _ , _ , trans (sym (↑idem ⌈ T ⌉)) h
FunClosed h (Trans d d₁)
  with FunClosed h d
... | b , U , V , eq = FunClosed eq d₁

N<:Funbot : {A B : Tp} {T' T'' : Tp!} {x x₁ : 𝔹} →
  ⌈ A ⌉ ≡ x !N → ⌈ B ⌉ ≡ x₁ ! T' ⇒ T'' → A <: B
  → ⊥ {lzero}
N<:Funbot h1 h2 h3
  with NatClosed h1 h3
... | b , eqNat = funNotNat (trans (sym h2) eqNat)

Fun<:Nbot : {A B : Tp} {T' T'' : Tp!} {x x₁ : 𝔹} →
  ⌈ A ⌉ ≡ x ! T' ⇒ T'' → ⌈ B ⌉ ≡ x₁ !N → A <: B
  → ⊥ {lzero}
Fun<:Nbot h1 h2 h3
  with FunClosed h1 h3
... | b , U , V , eqFun = funNotNat (trans (sym eqFun) h2)

nfOk-refl : ∀ (b : 𝔹) → natFlagOk b Nothing b
nfOk-refl tt = triv
nfOk-refl ff = triv

nfOk-pure : ∀ (b : 𝔹) → natFlagOk b Nothing tt
nfOk-pure tt = triv
nfOk-pure ff = triv

refl! : ∀ {A : Tp!} → A < Nothing :! A
refl! {b !N}      = Nat! (nfOk-refl _)
refl! {b ! A ⇒ B} = Fun! {j = Ord} (nfOk-refl _ , nfOk-refl _) refl! refl!

pure! : ∀ {A : Tp!} → A < Nothing :! ↑ A
pure! {b !N}      = Nat! (nfOk-pure _)
pure! {b ! A ⇒ B} = Fun! {j = Ord} (nfOk-pure _ , nfOk-refl _) refl! refl!

leftLem : ∀ {A : Tp!} → A < Left :! ↑ A
leftLem {b !N}      = Nat! triv
leftLem {b ! A ⇒ B} = Fun! {j = Ord} (triv , nfOk-refl _) refl! refl!

rightLem : ∀ {A : Tp!} → ↑ A < Right :! A
rightLem {b !N}      = Nat! triv
rightLem {b ! A ⇒ B} = Fun! {j = Ord} (triv , nfOk-refl _) refl! refl!

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
... | Cov (Fun h h₁) = {!!}
... | Cov (Trans h h₁) = {!!}
... | Trans h h₁ = {!!}
completeness {Nothing} {tt ! T ⇒ T₁} {ff ! T' ⇒ T''} eq = {!!}
completeness {Nothing} {ff ! T ⇒ T₁} {tt ! T' ⇒ T''} eq = {!!}
completeness {Nothing} {ff ! T ⇒ T₁} {ff ! T' ⇒ T''} eq
  with eq {⟦ T ⟧ ⇒ ⟦ T₁ ⟧} {⟦ T' ⟧ ⇒ ⟦ T'' ⟧} norm-norm norm-norm
... | Fun h h₁ = {!!}
... | Trans h h₁ = {!!}
