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
  Join : ∀{T : Tp} → L L T <: L T
  Trans : ∀{T1 T2 T3 : Tp} → T1 <: T2 → T2 <: T3 → T1 <: T3

refl-all : ∀{T} → T <: T
refl-all {N} = NatRefl
refl-all {L T} = Cov (refl-all{T})
refl-all {T ⇒ T'} = Fun (refl-all{T}) (refl-all{T'})

