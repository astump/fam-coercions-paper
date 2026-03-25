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