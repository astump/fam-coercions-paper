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
zero ↑ a = a
suc m ↑ n ! a = m ↑ (suc n ! a)

data coe' : ty' → ty' → Set
data coe! : ty! → ty! → Set

data coe' where
  c-base : coe' base base
  c-⇒ : {a b u v uu vv : ty!} →
    (k : ℕ) →
    uu ≡ k ↑ u →
    vv ≡ k ↑ v →
    coe! u a →
    coe! b v →
    coe' (a ⇒ b) (uu ⇒ vv)

data coe! where
  c-zero : {a b : ty'} →
    coe' a b →
    coe! (zero ! a) (zero ! b)
  c-suc : {a b : ty'} →
    (n : ℕ) →
    coe! (n ! a) (n ! b) →
    coe! (suc n ! a) (suc n ! b)

c-! : ∀ {n m a b} → n ≡ m → coe' a b → coe! (n ! a) (m ! b)
c-! {zero} {zero} refl c = c-zero c
c-! {suc n} {suc n} refl c = c-suc n (c-! refl c)

depth : ty! → ℕ
depth (n ! t) = n

strip : ty! → ty'
strip (n ! t) = t
