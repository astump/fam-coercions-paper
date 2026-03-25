{- prove soundness of the decision procedure with respect to the
   declarative semantics -}

module Soundness where
open import lib

open import Tp
open import Declarative
open import Decproc
open import Semantics

{-
+ℤcomm : ∀{i j : ℤ} → i +ℤ j ≡ j +ℤ i
+ℤcomm = {!!}
-}

Distrib-iter : ∀{k : ℕ}{T : Tp} →
               Distrib k T (iter k L_ T)
Distrib-iter = {!!}

Soundness : ∀{k : ℤ}{T T' : Tp!} → T < k ] T' → ⊨ T < k ] T'
Soundness {mkℤ zero triv} (NatRefl{n}{m} x) rewrite +ℤ0{toℤ m} with toℤ-≤{n}{m} x 
Soundness {mkℤ zero triv} (NatRefl{n}{m} x) | u = ≤iterL{n}{m} u
Soundness {mkℤ zero triv} (Fun nz jb d d') = {!!}
Soundness {mkℤ (suc k) tt} (NatRefl{n}{m} x) = 
 (iter (suc k + m) L_ N) , h , ≤iterL {n} {suc k + m} (toℤ-≤ {n} {suc k + m} {!!})
 where h : Distrib (suc k) (iter m L_ N) (L iter (k + m) L_ N)
       h rewrite sym (iter-add{k}{m}{f = L_}{N}) = Distrib-iter
Soundness {mkℤ (suc k) tt } (Fun nz jb d d') = {!!}
Soundness {mkℤ (suc k) ff} (NatRefl{n}{m} x) = {!!}
Soundness {mkℤ (suc k) ff } (Fun nz jb d d') = {!!}