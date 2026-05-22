open import lib
open import Tp

module Declarative where

infix 5 _<:_ 

data _<:_ : Tp → Tp → Set where
  NatRefl : N <: N
  Fun : ∀{T1 T2 T1' T2' : Tp} → 
         T1' <: T1 →
         T2 <: T2' →
         T1 ⇒ T2 <: T1' ⇒ T2'
  Seq : ∀{T1 T2 : Tp} → L (T1 ⇒ T2) <: L T1 ⇒ L T2
  Pure : ∀{T : Tp} → T <: L T
  Cov : ∀{T1 T2 : Tp} → T1 <: T2 → L T1 <: L T2
  Join : ∀{T : Tp} → L L T <: L T
  Trans : ∀{T1 T2 T3 : Tp} → T1 <: T2 → T2 <: T3 → T1 <: T3

refl-all : ∀{T} → T <: T
refl-all {N} = NatRefl
refl-all {L T} = Cov (refl-all{T})
refl-all {T ⇒ T'} = Fun (refl-all{T}) (refl-all{T'})

{-
TP! ENCODING: 
With a monad L, 
  Lⁿ T <: Lᵐ T   if m ≠ 0 or n = 0 (via Pure and Join)

Thus, we can encode the number of applications of L with a boolean: 
  ff !N represents N without applications
  tt !N represents Lⁿ N for some n > 0

There are three types of coersions:
  1. pos : T <: L T 
  2. zero : T <: T
  3. neg : L T <: T

We write these as T < s ] T' where s ∈ {pos, zero, neg}:

REFLEXIVITY RULE:

We want 
   b! N < zero ] b'! N 
to hold when
  b = ff              N <: Lⁿ N (via pure)
  b = tt ∧ b' = tt    Lⁿ N <: Lᵐ N where n, m ≠ 0 (via join/pure)
but not when
  b = tt ∧ b' = ff    Lⁿ N <: N does not hold for n > 0 

We want 
   b! N < pos ] b'! N 
to always be true because whe
  b = tt ∧ b' = ff    Lⁿ N <: L N (via join/pure)

We want 
  b! N < neg ] b'! N
to hold when
  b' = tt             Lⁿ N <: Lⁿ N (via join/pure)
but now when
  b' = ff             LⁿN  <: N 

So we define a helper function cond:
  Cond : Sign → Bool → Bool → Bool :=
  Cond zero tt ff = ff
  cond zero _ _ = tt
  cond pos _ _ = tt
  cond neg _ ff = ff
  cond neg _ tt = tt 

then our reflexivity rule is:
  NatRefl : cond s b b' ≡ tt → b! N < s ] b'! N 

FUNCTION RULES:

Modify the declarative function rule to work with the new encoding. 

Fun : cond s b b' ≡ tt
      → T1' < zero ] T1
      → T2  < zero ] T2'
      → (b ! T1 ⇒ T2) < s ] (b' ! T1' ⇒ T2')

We use the same cond function to make sure that the outer L adjustment is legit.

The second rule corresponds to using seq along with the function rule.
Seq distributes one L into the domain and out of the codomain. 
This rule requires no outer condition because seq can always be prefaced with pure or join.

  FunSeq : T1' < pos ] T1
         → T2  < neg ] T2'
         → (b ! T1 ⇒ T2) < s ] (b' ! T1' ⇒ T2')

We prove the sequence rule:
L(T1 ⇒ T2) <: L T1 ⇒ L T2
becomes
  tt! (ff!T1 ⇒ ff!T2) <zero] ff! (tt!T1 ⇒ tt!T2)

Proof: apply FunSeq with two subgoals:

  p1 (domain): tt!T1 <pos] ff!T1
    by NatRefl: cond pos tt ff = tt   (pos is always tt)

  p2 (codomain): ff!T2 <neg] tt!T2
    by NatRefl: cond neg ff tt = tt    (neg requires b' = tt, which it is)

FunSeq requires no outer condition on b or s or b', so the outer
(tt, zero, ff) is accepted unconditionally.
-}