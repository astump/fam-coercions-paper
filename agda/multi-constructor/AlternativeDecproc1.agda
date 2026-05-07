module Decproc where

open import lib
open import Tp

subSeqSet : ∀{T : Set} → list T → list T → Set
subSeqSet [] ys = ⊤
subSeqSet (x :: xs) [] = ⊥
subSeqSet (x :: xs) (y :: ys) = (x ≡ y ∧ subSeqSet xs ys) ∨ subSeqSet (x :: xs) ys


data _<]_ : Tp! → Tp! → Set where

 NatRefl : ∀{l1 l2 : list Ctor} →
           subSeqSet l1 l2 →
           l1 !N  <] l2 !N
 
 Fun : ∀{l1 l2 lj : list Ctor}{T1 T2 T1' T2' : Tp!} →
       subSeqSet l1 (l2 ++ lj) →
       T1' <] pushTop lj T1 →
       pushTop lj T2 <] T2' →
       l1 ! T1 ⇒ T2 <] l2 ! T1' ⇒ T2'


