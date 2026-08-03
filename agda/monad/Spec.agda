module Spec where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics

infix 5 ⊨_<_:!_
⊨_<_:!_ : Tp! → Flag → Tp! → Set
⊨ T < Nothing :! T' = ∃ Tp (λ S → ∃ Tp (λ S' →
                       T ≺ S ∧
                       T' ≺ S' ∧
                       S <: S'))
⊨ T < Left :! T' = ∃ Tp (λ S → ∃ Tp (λ S' →
                       (↑ T) ≺ S ∧
                       T' ≺ S' ∧
                       S <: S'))
⊨ T < Right :! T' = ∃ Tp (λ S → ∃ Tp (λ S' →
                       T ≺ S ∧
                       (↑ T') ≺ S' ∧
                       S <: S'))
