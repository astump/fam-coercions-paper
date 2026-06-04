module Constraints where

open import lib hiding (_∘_ ; _>>=_ ; return)
open import Monad

instance
  maybeMonad : Monad maybe 
  maybeMonad = record { return = return-maybe ; _>>=_ = _≫=maybe_ }

Const : Set
Const = ℕ

infix 9 V_
infixr 7 _∘_
infixr 8 _▸_
infixr 6 _//_
infixl 6 _\\_

data Expr : Set where
  V_ : ℕ → Expr                 -- variables
  _∘_ : Expr → Expr → Expr       -- concatenation
  _▸_ : Const → Expr → Expr      -- adding a constant to the left
  ε : Expr                       -- empty sequence
  _//_ : Expr → Expr → Expr      -- removing the left sequence from the right (subl below)
  _\\_ : Expr → Expr → Expr      -- removing the right sequence from the left (subr)

Seq : Set
Seq = 𝕃 Const

-- the n'th item in the list is the value for variable n
Valuation : Set
Valuation = 𝕃 Seq






-- remove the Consts in the first Seq from the second if possible, leaving all
-- other Consts in place.
subl : Seq → Seq → maybe Seq
subl [] ys = return ys
subl (x :: u) [] = nothing  -- failure case
subl (x :: u) (y :: v) with x =ℕ y
subl (x :: u) (y :: v) | tt = subl u v
subl (x :: u) (y :: v) | ff = subl (x :: u) v

-- like subl, but remove the Consts in the right from the left,
-- working from right to left in the sequences
subr : Seq → Seq → maybe Seq
subr xs ys =
  do
    r ← subl (reverse ys) (reverse xs)
    return (reverse r)

⟦_⟧ : Expr → Valuation → maybe Seq
⟦ V n ⟧ v = nth n v
⟦ e ∘ e₁ ⟧ v =
  do
    r ← ⟦ e ⟧ v
    r₁ ← ⟦ e₁ ⟧ v
    return (r ++ r₁)
⟦ x ▸ e ⟧ v =
  do
    r ← ⟦ e ⟧ v
    return (x :: r)
⟦ ε ⟧ v = return []
⟦ e // e₁ ⟧ v =
  do
    r ← ⟦ e ⟧ v
    r₁ ← ⟦ e₁ ⟧ v
    subl r r₁
⟦ e \\ e₁ ⟧ v =
  do
    r ← ⟦ e ⟧ v
    r₁ ← ⟦ e₁ ⟧ v
    subr r r₁

infix 5 _≪_

-- e ≪ e' means that the meaning of e is a subsequence of meaning of e'
data Constraint : Set where
  _≪_ : Expr → Expr → Constraint

infix 4 _⊨_

-- what is the truth value of a constraint, with respect to a given valuation?
-- we just check if subtracting (subl) the meaning of e from that of e' is defined
_⊨_ : Valuation → Constraint → 𝔹
v ⊨ e ≪ e' with ⟦ e // e' ⟧ v
v ⊨ e ≪ e' | just _ = tt
v ⊨ e ≪ e' | nothing = ff
    
subl++ : ∀{s1 s2 s : Seq} →
          (subl (s1 ++ s2) s) ≡ (subl s1 s) >>= (subl s2)
subl++ {[]} {s2} {s} = refl
subl++ {x :: s1} {s2} {[]} = refl
subl++ {x :: s1} {s2} {y :: s} with x =ℕ y 
subl++ {x :: s1} {s2} {y :: s} | tt = subl++{s1}{s2}{s}
subl++ {x :: s1} {s2} {y :: s} | ff = subl++{x :: s1}{s2}{s}

splitLem : ∀{e1 e2 e' : Expr}{v : Valuation} →
           v ⊨ e1 ∘ e2 ≪ e' ≡ tt →
           v ⊨ e2 ≪ e1 // e' ≡ tt
splitLem{e1}{e2}{e'} p = {!!}
