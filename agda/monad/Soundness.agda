module Soundness where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics
open import Spec

soundness : ∀{f : Flag}{T T' : Tp!} →
            T < f :! T' →
            ⊨ T < f :! T'
soundness {f = Left} {T = b !N} {T' = ff !N} (Nat! ())
soundness {f = Left} {T = b !N} {T' = tt !N} (Nat! ok) =
    L N , L N , refl , refl , refl-raw
soundness {f = Right} {T = ff !N} {T' = b' !N} (Nat! ok) =
    N , L N , refl , refl , Pure
soundness {f = Right} {T = tt !N} {T' = b' !N} (Nat! ok) =
    L N , L N , refl , refl , refl-raw
soundness {f = Nothing} {T = tt !N} {T' = ff !N} (Nat! ())
soundness {f = Nothing} {T = ff !N} {T' = ff !N} (Nat! ok) =
    N , N , refl , refl , NatRefl
soundness {f = Nothing} {T = ff !N} {T' = tt !N} (Nat! ok) =
    N , L N , refl , refl , Pure
soundness {f = Nothing} {T = tt !N} {T' = tt !N} (Nat! ok) =
    L N , L N , refl , refl , refl-raw
soundness {Left} (Fun! {tt} {tt} {j = Ord} {A} {B} {A'} {B'} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
  rewrite (sym eqA) | (sym eqA') | (sym eqB) | (sym eqB') =
      L (DA ⇒ CB) , L (DA' ⇒ CB') , refl , refl , Cov (Fun dDom dCod)
soundness {Right} (Fun! {b = tt} {b' = tt} {j = Ord} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
  rewrite (sym eqA) | (sym eqA') | (sym eqB) | (sym eqB') =
    L (DA ⇒ CB) , L (DA' ⇒ CB') , refl , refl , Cov (Fun dDom dCod)
soundness {Nothing} (Fun! {b = tt} {b' = tt} {j = Ord} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
  rewrite (sym eqA) | (sym eqA') | (sym eqB) | (sym eqB') =
    L (DA ⇒ CB) , L (DA' ⇒ CB') , refl , refl , Cov (Fun dDom dCod)
soundness {Right} (Fun! {b = tt} {b' = ff} {j = Ord} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
  rewrite (sym eqA) | (sym eqA') | (sym eqB) | (sym eqB') =
    L (DA ⇒ CB) , L (DA' ⇒ CB') , refl , refl , Cov (Fun dDom dCod)
soundness {Left} (Fun! {b = ff} {b' = tt} {j = Ord} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
  rewrite (sym eqA) | (sym eqA') | (sym eqB) | (sym eqB') =
    L (DA ⇒ CB) , L (DA' ⇒ CB') , refl , refl , Cov (Fun dDom dCod)
soundness {Right} (Fun! {b = ff} {b' = tt} {j = Ord} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
  rewrite (sym eqA) | (sym eqA') | (sym eqB) | (sym eqB') =
    DA ⇒ CB , L (DA' ⇒ CB') , refl , refl , Trans (Fun dDom dCod) Pure
soundness {Nothing} (Fun! {b = ff} {b' = tt} {j = Ord} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
  rewrite (sym eqA) | (sym eqA') | (sym eqB) | (sym eqB') =
    DA ⇒ CB , L (DA' ⇒ CB') , refl , refl , Trans (Fun dDom dCod) Pure
soundness {Right} (Fun! {b = ff} {b' = ff} {j = Ord} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
  rewrite (sym eqA) | (sym eqA') | (sym eqB) | (sym eqB') =
    DA ⇒ CB , L (DA' ⇒ CB') , refl , refl , Trans (Fun dDom dCod) Pure
soundness {Nothing} (Fun! {b = ff} {b' = ff} {j = Ord} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
  rewrite (sym eqA) | (sym eqA') | (sym eqB) | (sym eqB') =
    DA ⇒ CB , DA' ⇒ CB' , refl , refl , Fun dDom dCod
soundness {Left} (Fun! {b = tt} {b' = ff} {j = Ord} ok dom cod) = ⊥-elim ok
soundness {Left} (Fun! {b = ff} {b' = ff} {j = Ord} ok dom cod) = ⊥-elim ok
soundness {Nothing} (Fun! {b = tt} {b' = ff} {j = Ord} ok dom cod) = ⊥-elim ok
soundness {Left} (Fun! {tt} {ff} {j = Seq} {A} {B} {A'} {B'} ok dom cod)
  with soundness dom | soundness cod
... | DA' , DA , eqA' , eqA , dDom
    | CB  , CB' , eqB  , eqB' , dCod
-- Problem: I dont think I can find an S such that ⌈ S ⌉ ≡ tt ! A ⇒ B
  = {!!}
soundness {Left} (Fun! {ff} {ff} {j = Seq} ok dom cod) = {!!}
soundness {Nothing} (Fun! {tt} {ff} {j = Seq} ok dom cod) = {!!}
