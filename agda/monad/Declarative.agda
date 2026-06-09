module Declarative where

open import lib
open import Tp

infix 5 _<:_

data _<:_ : Tp → Tp → Set where
  NatRefl : N <: N

  Fun : ∀{T1 T2 T1' T2' : Tp} →
        T1' <: T1 →
        T2  <: T2' →
        T1 ⇒ T2 <: T1' ⇒ T2'

  Seq : ∀{T1 T2 : Tp} →
        L (T1 ⇒ T2) <: L T1 ⇒ L T2

  Pure : ∀{T : Tp} →
         T <: L T

  Cov : ∀{T1 T2 : Tp} →
        T1 <: T2 →
        L T1 <: L T2

  Join : ∀{T : Tp} →
         L (L T) <: L T

  Trans : ∀{T1 T2 T3 : Tp} →
          T1 <: T2 →
          T2 <: T3 →
          T1 <: T3

-- Reflexivity is admissible for the declarative relation.
refl-raw : ∀{T} → T <: T
refl-raw {N}      = NatRefl
refl-raw {L T}    = Cov refl-raw
refl-raw {T ⇒ T'} = Fun refl-raw refl-raw
