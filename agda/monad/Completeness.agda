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
completeness {Left} {T} {T'} (S , S' , exp , exp' , d) = {!!}
completeness {Right} {T} {T'} (S , S' , exp , exp' , d) = {!!}
completeness {Nothing} {T} {T'} (N , N , refl , refl , NatRefl) = Nat! triv
completeness {Nothing} {T} {T'} (S , S' , exp , exp' , Fun d d₁) = {!!}
completeness {Nothing} {T} {T'} (S , S' , exp , exp' , Seq) = {!!}
completeness {Nothing} {T} {T'} (S , S' , exp , exp' , Pure) = {!!}
completeness {Nothing} {T} {T'} (S , S' , exp , exp' , Cov d) = {!!}
completeness {Nothing} {T} {T'} (S , S' , exp , exp' , Join) = {!!}
completeness {Nothing} {T} {T'} (S , S' , exp , exp' , Trans d d₁) = {!!}
