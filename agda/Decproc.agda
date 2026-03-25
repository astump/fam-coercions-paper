module Decproc where

open import lib
open import Tp

infix 8 _<_]_ 

data _<_]_ : Tp! → ℤ → Tp! → Set where

 NatRefl : ∀ {n m : ℕ}{k : ℤ} →
          (toℤ n) ≤ℤ k +ℤ (toℤ m) ≡ tt →            -- n ≤ k + m 
          n !N  < k ]  m !N

 Fun : ∀{n m : ℕ}{j k : ℤ}{T1 T2 T1' T2' : Tp!} →
       j ≥ℤ 0ℤ ≡ tt →                               -- j ≥ 0
       j ≥ℤ (toℤ n) -ℤ k -ℤ (toℤ m) ≡ tt →          -- j ≥ n - k - m
       T1'           < j ]       T1  →
       T2            < negℤ j ]  T2' → 
       n ! T1 ⇒ T2   < k ]       m ! T1' ⇒ T2'

{-
refl-decproc : ∀{T : Tp} → ! T <: T
refl-decproc {N} = NatRefl
refl-decproc {L T} = Cov refl-decproc
refl-decproc {T ⇒ T'} = SeqFun (Decompose⇒ refl-decproc refl-decproc) 

-}