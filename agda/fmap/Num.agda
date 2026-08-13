module fmap.Num where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

data ty' : Set
data ty! : Set

data ty! where
  _!_ : ℕ → ty' → ty!

infixl 8 _⇒_

data ty' where
  base : ty'
  _⇒_ : ty! → ty! → ty'

infixr 9 _!_
infixr 9 _↑_

_↑_ : ℕ → ty! → ty!
m ↑ n ! a = (m + n) ! a

data coe' : ty' → ty' → Set
data coe! : ty! → ty! → Set

data coe' where
  c-base : coe' base base
  c-⇒ : {na nb : ℕ} {a b : ty'} {nu nv : ℕ} {u v : ty'} →
    (k : ℕ) →
    coe! (nu ! u) (na ! a) →
    coe! (nb ! b) (nv ! v) →
    coe' (na ! a ⇒ nb ! b) ((k + nu) ! u ⇒ (k + nv) ! v)

data coe! where
  c-! : ∀ {n m a b} →
    m ≡ n →
    coe' a b →
    coe! (n ! a) (m ! b)

depth : ty! → ℕ
depth (n ! t) = n

strip : ty! → ty'
strip (n ! t) = t
