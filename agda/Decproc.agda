module Decproc where

open import lib
open import Tp

infix 8 _!_<:_ 

data _!_<:_ : ℤ → Tp! → Tp! → Set where

 NatRefl : ∀ {n m : ℕ}{z : ℤ} →
          (toℤ n) ≤ℤ z +ℤ (toℤ m) ≡ tt →      -- n ≤ z + m 
          z ! n !N <: m !N

-- Fun : ∀{j k n m : ℕ}

{-
refl-decproc : ∀{T : Tp} → ! T <: T
refl-decproc {N} = NatRefl
refl-decproc {L T} = Cov refl-decproc
refl-decproc {T ⇒ T'} = SeqFun (Decompose⇒ refl-decproc refl-decproc) 

-}