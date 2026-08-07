module Spec where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics

infix 5 ⊨_<_:!_
⊨_<_:!_ : Tp! → Flag → Tp! → Set
⊨ T < Nothing :! T' =
  {A B : Tp} →
  ⌈ A ⌉ ≡ T →
  ⌈ B ⌉ ≡ T' →
  A <: B
⊨ T < Left :! T' =
  {A B : Tp} →
  ⌈ A ⌉ ≡ ↑ T →
  ⌈ B ⌉ ≡ T' →
  A <: B
⊨ T < Right :! T' =
  {A B : Tp} →
  ⌈ A ⌉ ≡ T →
  ⌈ B ⌉ ≡ ↑ T' →
  A <: B
