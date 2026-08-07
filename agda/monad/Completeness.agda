{-# OPTIONS --allow-unsolved-metas #-} -- remove when done

module Completeness where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics
open import Spec

completeness : ∀{f : Flag}{T T' : Tp!} →
               ⊨ T < f :! T' →
               T < f :! T'
completeness eq = {!!}
