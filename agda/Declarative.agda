open import lib
open import Tp

module Declarative where

infix 5 _<:_ 

data _<:_ : Tp → Tp → Set where
  NatRefl : N <: N
  Fun : ∀{T1 T2 T1' T2' : Tp} → 
         T1' <: T1 →
         T2 <: T2' →
         T1 ⇒ T2 <: T1' ⇒ T2'
  Seq : ∀{T1 T2 : Tp} → L (T1 ⇒ T2) <: L T1 ⇒ L T2
  Pure : ∀{T : Tp} → T <: L T
  Cov : ∀{T1 T2 : Tp} → T1 <: T2 → L T1 <: L T2
  Trans : ∀{T1 T2 T3 : Tp} → T1 <: T2 → T2 <: T3 → T1 <: T3

refl-all : ∀{T} → T <: T
refl-all {N} = NatRefl
refl-all {L T} = Cov (refl-all{T})
refl-all {T ⇒ T'} = Fun (refl-all{T}) (refl-all{T'})

fmap : ∀{T1 T2} → T1 ⇒ T2 <: L T1 ⇒ L T2
fmap = Trans Pure Seq

iter-fmap : ∀{k}{T1 T2} → T1 ⇒ T2 <: iter k L_ T1 ⇒ iter k L_ T2
iter-fmap {zero} = refl-all
iter-fmap {suc k} = Trans (iter-fmap{k}) fmap

iter-seq : ∀{k}{T1 T2} → iter k L_ (T1 ⇒ T2) <: iter k L_ T1 ⇒ iter k L_ T2
iter-seq {zero} = refl-all
iter-seq {suc k} = Trans (Cov (iter-seq{k})) Seq

iter-cov : ∀{k}{T1 T2} → T1 <: T2 → iter k L_ T1 <: iter k L_ T2
iter-cov {zero} p = p
iter-cov {suc k} p = Cov (iter-cov{k} p)

iter-pure : ∀{k}{T} → T <: iter k L_ T
iter-pure {zero} = refl-all
iter-pure {suc k} = Trans (iter-pure{k}) Pure

-- compute the size of a derivation
size : ∀{T T' : Tp} → T <: T' → ℕ
size NatRefl = 0
size (Fun d d') = 1 + size d + size d'
size Seq = 0
size Pure = 0
size (Cov d) = 1 + size d
size (Trans d d') = 1 + size d + size d'

≤iterL : ∀{n m : ℕ} → n ≤ m ≡ tt →
         iter n L_ N <: iter m L_ N
≤iterL {zero} {zero} d = NatRefl
≤iterL {zero} {suc m} d = Trans (≤iterL {zero} {m} (0≤{m})) Pure
≤iterL {suc n} {suc m} d = Cov (≤iterL {n} {m} (suc≤{n}{m} d))

{-
¬⇒iterN : ∀{n T1 T2} → ¬ (T1 ⇒ T2 ≡ iter n L_ N)
¬⇒iterN {zero} ()
¬⇒iterN {suc n} ()
-}

L≢ : ∀{T T' : Tp} → T ≢ T' → L T ≢ L T'
L≢ u refl = u refl

¬⇒iterN : ∀{m n T1 T2} → iter m L_ (T1 ⇒ T2) ≢ iter n L_ N
¬⇒iterN {suc m} {zero} ()
¬⇒iterN {suc m} {suc n} e = L≢ (¬⇒iterN{m}{n}) e 

N<: : ∀{n T T'} → T ≡ iter n L_ N → T <: T' → ∃ ℕ (λ m → m ≥ n ≡ tt ∧ T' ≡ iter m L_ N)
N<:{zero} e NatRefl = 0 , refl , refl
N<: {zero} {T1 ⇒ T2} {T1' ⇒ T2'} () (Fun d d₁) 
N<: {suc n} {T1 ⇒ T2} {T1' ⇒ T2'} () (Fun d d₁) 
N<: {suc n} e Seq = ⊥-elim (¬⇒iterN{1}{suc n} e)
N<:{n} refl Pure = suc n , ≤-suc n , refl
N<: {suc n} refl (Cov d) with N<:{n} refl d 
N<: {suc n} refl (Cov d) | a , x , refl = suc a , x , refl
N<:{n} e (Trans d d') with N<:{n} e d 
N<:{n} e (Trans d d') | (m , x , e') with N<:{m} e' d' 
N<:{n} e (Trans d d') | (m , x , e') | (m' , y , e'') = m' , ≤-trans{n} x y , e''

<:N : ∀{n T T'} → T' ≡ iter n L_ N → T <: T' → ∃ ℕ (λ m → T ≡ iter m L_ N)
<:N {zero} e NatRefl = 0 , refl
<:N {n} e (Trans d d') with <:N{n} e d'
<:N {n} e (Trans d d') | m , e' = <:N {m} e' d
<:N {suc n}{m} refl Pure = n , refl
<:N {suc n} refl (Cov d) with <:N{n} refl d
<:N {suc n} refl (Cov d) | m , e' = suc m , cong L_ e'

Linj : ∀{T T'} → L T ≡ L T' → T ≡ T'
Linj refl = refl

iterL-inj : ∀{n m : ℕ} → iter n L_ N ≡ iter m L_ N →
            n ≡ m
iterL-inj {zero} {zero} e = refl
iterL-inj {suc n} {suc m} e rewrite iterL-inj{n}{m} (Linj e) = refl
