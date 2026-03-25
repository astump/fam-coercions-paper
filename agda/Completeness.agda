{- prove completeness of the decision procedure with respect to the
   declarative semantics -}

module Completeness where
open import lib

open import Tp
open import Declarative
open import Decproc

Completeness : ∀{T T'} → T <: T' → ! T <: T'
Completeness NatRefl = NatRefl
Completeness{T1 ⇒ T2} (Fun d1 d2) = SeqFun (Decompose⇒{T1}) (Completeness d1) (Completeness d2)
Completeness{L (T1 ⇒ T2)} Seq = SeqFun (DecomposeL (Decompose⇒{T1})) refl-decproc refl-decproc
Completeness Pure = pure
Completeness (Cov d) = Cov (Completeness d)
Completeness (Trans d1 d2) = {!!}