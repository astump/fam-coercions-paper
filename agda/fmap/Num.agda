module fmap.Num where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

data ty' : Set
data ty! : Set

data ty! where
  _!_ : ℕ → ty' → ty!

data ty' where
  base : ty'
  _⇒_ : ty! → ty! → ty'

infixr 9 _!_
infixr 9 _↑_

_↑_ : ℕ → ty! → ty!
m ↑ n ! a = (m + n) ! a

data coe' : ty' → ty' → Set where
  c-base : coe' base base
  c-⇒ : {n m i j : ℕ} {a b u v : ty'} →
    (k : ℕ) →
    coe' u a →
    coe' b v →
      coe' ((n ! a) ⇒ (m ! b)) (((k + n) ! u) ⇒ ((k + m) ! v))

data coe! : ty! → ty! → Set where
  c-! : {n m : ℕ} {a b : ty'} →
    n ≡ m →
    coe' a b →
    coe! (n ! a) (m ! b)

depth : ty! → ℕ
depth (n ! t) = n

strip : ty! → ty'
strip (n ! t) = t
