module Tp where
open import lib

data Ctor : Set where
  F : ℕ → Ctor

data Tp : Set where
  N : Tp
  _of_ : Ctor → Tp → Tp
  _⇒_ : Tp → Tp → Tp

infixr 9 _⇒_
infixr 10 _of_

data Tp! : Set where
  _!N : 𝕃 Ctor → Tp!
  _!_⇒_ : 𝕃 Ctor → Tp! → Tp! → Tp!

infixr 9 _!_⇒_
infixr 10 _!N

_=F_ : Ctor → Ctor → 𝔹
(F x) =F (F y) = x =ℕ y

infixr 8 _=F_

_=T_ : Tp! → Tp! → 𝔹
l1 !N =T l2 !N = =𝕃 (_=F_) l1 l2
l1 !N =T l2 ! T2 ⇒ T3 = ff
l1 ! T1 ⇒ T2 =T l2 !N = ff
l1 ! T1 ⇒ T2 =T l2 ! T1' ⇒ T2' = =𝕃 (_=F_) l1 l2
                              && T1 =T T1'
                              && T2 =T T2'
infixr 8 _=T_


-- Applies constructor list to a type.
-- Note that the head of the list is applied last,
-- so that [Maybe, List] applied to Nat is Maybe List Nat
constrL : 𝕃 Ctor → Tp → Tp
constrL l = constrL' (reverse l)
      where constrL' : 𝕃 Ctor → Tp → Tp
            constrL' [] T = T
            constrL' (X :: Xs) T = constrL' Xs (X of T)

-- Adds constructors to the "top" of the type.
-- e.g.: Maybe List Nat  --->  Maybe List Maybe (Maybe List Nat)
pushTop : 𝕃 Ctor → Tp! → Tp!
pushTop top (l !N) = (top ++ l) !N
pushTop top (l ! T1 ⇒ T2) = (top ++ l) ! T1 ⇒ T2

