module Declarative where
open import lib
open import Tp

infix 5 _<:_ 

data _<:_ : Tp → Tp → Set where
  NatRefl : N <: N
  Fun : ∀{T1 T2 T1' T2' : Tp} → 
         T1' <: T1 →
         T2 <: T2' →
         T1 ⇒ T2 <: T1' ⇒ T2'
  Seq : ∀{T1 T2 : Tp}{F : Ctor} → F of (T1 ⇒ T2) <: F of T1 ⇒ F of T2
  Pure : ∀{T : Tp}{F : Ctor} → T <: F of T
  Cov : ∀{T1 T2 : Tp}{F : Ctor} → T1 <: T2 → F of T1 <: F of T2
  Trans : ∀{T1 T2 T3 : Tp} → T1 <: T2 → T2 <: T3 → T1 <: T3
