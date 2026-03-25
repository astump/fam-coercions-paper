module DecprocTrans where

open import lib
open import Tp
open import Decproc

mutual
 trans-decproc : ∀{T T' T''} → ! T <: T' → ! T' <: T'' → ! T <: T''
 trans-decproc {T} {N} {T''} NatRefl d' = d'
 trans-decproc {L T} {L T'} {T''} (Cov d) d' = trans2 d d'
 trans-decproc {T} {L T'} {T''} (Pure d) d' = trans1 d d'
 trans-decproc {T} {T1 ⇒ T2} {T''} (SeqFun x) d' = {!!}

 trans1 : ∀{T T' T''} → ! T <: T' → ! L T' <: T'' → ! T <: T''
 trans1 {T} {T'} {L T''} d (Cov d') = Pure (trans-decproc d d')
 trans1 {T} {T'} {T1' ⇒ T2'} d (SeqFun x) = {!!}
 trans1 {T} {T'} {L T''} d (Pure d') = trans3 d d'

 trans2 : ∀{T T' T''} → ! T <: T' → ! L T' <: T'' → ! L T <: T''
 trans2 {T} {T'} {L T''} d (Cov d') = Cov (trans-decproc d d')
 trans2 {T} {T'} {T1' ⇒ T2'} d (SeqFun x) = {!!}
 trans2 {T} {T'} {T''} d (Pure d') = {!!}

 trans3 : ∀{T T' T''} → ! T <: T' → ! L T' <: T'' → ! T <: L T''
 trans3 {T} {T'} {L T''} d (Cov d') = {!!}
 trans3 {T} {T'} {L T''} d (Pure d') = {!!}
 trans3 {T} {T'} {T1' ⇒ T2'} d (SeqFun x) = {!!}

 trans4 : ∀{T T1 T2 T'} →
          Decompose T T1 T2 →
          ! T1 ⇒ T2 <: T' →
          ! T <: T'
 trans4 x (Pure d) = Pure (trans4 x d)
 trans4 x (SeqFun y) = SeqFun (trans5 x y)

 trans5 : ∀{T T1 T2 T1' T2'} →
          Decompose T T1 T2 →
          Decompose (T1 ⇒ T2) T1' T2' →
          Decompose T T1' T2'
 trans5 x (DecomposeP y x₁ x₂) = {!!}
 trans5 x (Decompose⇒ x₁ x₂) = {!!}