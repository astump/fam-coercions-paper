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
-- remove the Consts in the first Seq from the second if possible, removing
-- extraneous Consts
subll : Seq → Seq → maybe Seq
subll [] ys = return ys
subll (x :: u) [] = nothing  -- failure case
subll (x :: u) (y :: v) with x =ℕ y
subll (x :: u) (y :: v) | tt = subll u v
subll (x :: u) (y :: v) | ff = subll (x :: u) v

sub-flip : (Seq → Seq → maybe Seq) → Seq → Seq → maybe Seq
sub-flip f xs ys =
  do
    r ← f (nreverse ys) (nreverse xs)
    return (nreverse r)

-- like subl, but remove the Consts in the right from the left,
-- working from right to left in the sequences
sublr : Seq → Seq → maybe Seq
sublr = sub-flip subll

subrl : Seq → Seq → maybe Seq
subrl [] ys = return ys
subrl (x :: xs) [] = return []
subrl (x :: xs) (y :: ys) with x =ℕ y 
subrl (x :: xs) (y :: ys) | tt = subrl xs ys
subrl (x :: xs) (y :: ys) | ff = subrl xs (y :: ys)

subrr : Seq → Seq → maybe Seq
subrr = sub-flip subrl

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
    subll r r₁
⟦ e \\ e₁ ⟧ v =
  do
    r ← ⟦ e ⟧ v
    r₁ ← ⟦ e₁ ⟧ v
    sublr r r₁

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
    
subll++ : ∀{s1 s2 s : Seq} →
          (subll (s1 ++ s2) s) ≡ (subll s1 s) >>= (subll s2)
subll++ {[]} {s2} {s} = refl
subll++ {x :: s1} {s2} {[]} = refl
subll++ {x :: s1} {s2} {y :: s} with x =ℕ y 
subll++ {x :: s1} {s2} {y :: s} | tt = subll++{s1}{s2}{s}
subll++ {x :: s1} {s2} {y :: s} | ff = subll++{x :: s1}{s2}{s}

sublr++ : ∀{s1 s2 s : Seq} →
          (sublr s (s1 ++ s2)) ≡ (sublr s s2) >>= (sublr s1)
sublr++{s1}{s2}{s} rewrite nreverse-++ s1 s2 | subll++ {nreverse s2} {nreverse s1} {nreverse s} with subll (nreverse s2) (nreverse s) | (λ (r : Seq) → just (nreverse r))
sublr++{s1}{s2}{s} | p | q = {!!}

splitLem : ∀{e1 e2 e' : Expr}{v : Valuation} →
           v ⊨ e1 ∘ e2 ≪ e' ≡ tt →
           v ⊨ e2 ≪ e1 // e' ≡ tt
splitLem{e1}{e2}{e'} p = {!!}
