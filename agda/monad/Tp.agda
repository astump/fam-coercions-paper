module Tp where
open import lib

data Tp : Set where
  N : Tp
  L_ : Tp → Tp
  _⇒_ : Tp → Tp → Tp

infixr 9 _⇒_
infixr 10 L_

data Tp! : Set where
  _!N : 𝔹 → Tp!
  _!_⇒_ : 𝔹 → Tp! → Tp! → Tp!

infixr 9 _!_⇒_
infixr 10 _!N
