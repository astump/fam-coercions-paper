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

infix 5 _<]_ 
data _<]_ : Tp! → Tp! → Set where

 NatRefl : ∀{l1 l2 : list Ctor} →
           subSeqSet l1 l2 →
           l1 !N  <] l2 !N
 
 Fun : ∀{l1 l2 j : list Ctor}{T1 T2 T1' T2' : Tp!} →
       subSeqSet l1 (l2 ++ j) →
       T1' <] pushTop j T1 →
       pushTop j T2 <] T2' →
       l1 ! T1 ⇒ T2 <] l2 ! T1' ⇒ T2'


-- Alternative definition:
-- 
-- subSeqSetWith : ∀{T : Set} → list T → list T → list T → 𝔹 → Set
-- subSeqSetWith l1 l2 lk tt = subSeqSet l1 (lk ++ l2)
-- subSeqSetWith l1 l2 lk ff = subSeqSet (lk ++ l1) l2
-- 
-- 
-- infix 5 _<_$_]_ 
-- data _<_$_]_ : Tp! → list Ctor → 𝔹 → Tp! → Set where
-- 
--  NatRefl : ∀ {l1 l2 lk : list Ctor} {b : 𝔹} →
--            subSeqSetWith l1 l2 lk b →
--            l1 !N  < lk $ b ] l2 !N
-- 
--  Fun : ∀ {l1 l2 lk j : list Ctor} {T1 T2 T1' T2' : Tp!} {b : 𝔹} →
--        subSeqSetWith l1 (l2 ++ j) lk b →
--        T1' < j $ tt ] T1  →
--        T2  < j $ ff ] T2' →
--        l1 ! T1 ⇒ T2 < lk $ b ] l2 ! T1' ⇒ T2'



-- Alternative definition:
-- Would have to use snoc lists for logic program
-- 
-- infix 5 _<_$_]_ 
-- data _<_$_]_ : Tp! → list Ctor → 𝔹 → Tp! → Set where
-- 
--  NatRefl : ∀ {l1 l2 lk : list Ctor} {b : 𝔹} →
--             subSeqSet l1 l2 →
--             l1 !N  < [] $ b ] l2 !N
-- 
--  Fun : ∀ {l1 l2 j : list Ctor} {T1 T2 T1' T2' : Tp!}{b : 𝔹} →
--        subSeqSet l1 (l2 ++ j) →
--        T1' < j $ tt ] T1  →
--        T2  < j $ ff ] T2' →
--        l1 ! T1 ⇒ T2 < [] $ b ] l2 ! T1' ⇒ T2'
-- 
--  -- The following 4 rules could be combined into 2 if
--  -- constructors weren't baked into the Tp! data type directly.
-- 
--  PushRNat : ∀{l1 l2 lk : list Ctor} {x : Ctor} →
--             l1 !N < lk $ tt ] (x :: l2) !N →
--             l1 !N < lk ++ [ x ] $ tt ] l2 !N
-- 
--  PushRFun : ∀ {l1 l2 lk : list Ctor} {x : Ctor} {T1 T2 T1' T2' : Tp!} →
--             l1 ! T1 ⇒ T2 < lk $ tt ] (x :: l2) ! T1' ⇒ T2' →
--             l1 ! T1 ⇒ T2 < lk ++ [ x ] $ tt ] l2 ! T1' ⇒ T2'
-- 
--  PushLNat : ∀ {l1 l2 lk : list Ctor} {x : Ctor} →
--             (x :: l1) !N < lk $ ff ] l2 !N →
--             l1 !N < lk ++ [ x ] $ ff ] l2 !N
-- 
--  PushLFun : ∀ {l1 l2 lk : list Ctor} {x : Ctor} {T1 T2 T1' T2' : Tp!} →
--             (x :: l1) ! T1 ⇒ T2 < lk $ ff ] l2 ! T1' ⇒ T2' →
--             l1 ! T1 ⇒ T2 < lk ++ [ x ] $ ff ] l2 ! T1' ⇒ T2'
