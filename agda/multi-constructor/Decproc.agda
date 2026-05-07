module Decproc where

open import lib
open import Tp

-- Whether one list is a subsequence (can be obtained by removing elements) of the other.
subSeq : ∀{T : Set} → (T → T → 𝔹) → list T → list T → 𝔹
subSeq eq [] ys = tt
subSeq eq (x :: xs) [] = ff
subSeq eq (x :: xs) (y :: ys) = if eq x y
                                then subSeq eq xs ys
                                else subSeq eq (x :: xs) ys

subSeqSet : ∀{T : Set} → list T → list T → Set
subSeqSet [] ys = ⊤
subSeqSet (x :: xs) [] = ⊥
subSeqSet (x :: xs) (y :: ys) = (x ≡ y ∧ subSeqSet xs ys) ∨ subSeqSet (x :: xs) ys


subSeqSetWith : ∀{T : Set} → list T → list T → list T → 𝔹 → Set
subSeqSetWith l1 l2 lk tt = subSeqSet l1 (lk ++ l2)
subSeqSetWith l1 l2 lk ff = subSeqSet (lk ++ l1) l2


infix 5 _<_$_]_ 
data _<_$_]_ : Tp! → list Ctor → 𝔹 → Tp! → Set where

 NatRefl : ∀ {l1 l2 lk : list Ctor} {b : 𝔹} →
           subSeqSetWith l1 l2 lk b →
           l1 !N  < lk $ b ] l2 !N

 Fun : ∀ {l1 l2 lk lj : list Ctor} {T1 T2 T1' T2' : Tp!} {b : 𝔹} →
       subSeqSetWith l1 (l2 ++ lj) lk b →
       T1' < lj $ tt ] T1  →
       T2  < lj $ ff ] T2' →
       l1 ! T1 ⇒ T2 < lk $ b ] l2 ! T1' ⇒ T2'



