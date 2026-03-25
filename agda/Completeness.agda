{- prove completeness of the decision procedure with respect to the
   declarative semantics -}

module Completeness where
open import lib

open import Tp
open import Declarative
open import Decproc
open import Semantics

Completeness : ∀{k : ℤ}{T T' : Tp!} → T < k ] T' → ⊨ T < k ] T'
Completeness = {!!}