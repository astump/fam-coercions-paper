{- prove soundness of the decision procedure with respect to the
   declarative semantics -}

module Soundness where
open import lib

open import Tp
open import Declarative
open import Decproc
open import Semantics

open import ExtraIntegerLemmas


Distrib-iter : ∀{k : ℕ}{T : Tp} →
               Distrib k T (iter k L_ T)
Distrib-iter {zero} = Distrib0 refl
Distrib-iter {suc k} = DistribH Distrib-iter

Soundness : ∀{k : ℤ}{T T' : Tp!} → T < k ] T' → ⊨ T < k ] T'
Soundness {mkℤ zero triv} (NatRefl{n}{m} x) with toℤ-≤{n}{m} x 
Soundness {mkℤ zero triv} (NatRefl{n}{m} x) | u = ≤iterL{n}{m} u
Soundness {mkℤ (suc k) tt} (NatRefl{n}{m} x) = 
 (iter (suc k + m) L_ N) , h1 , ≤iterL {n} {suc k + m} (toℤ-≤ {n} {suc k + m} h2)
 where h1 : Distrib (suc k) (iter m L_ N) (L iter (k + m) L_ N)
       h1 rewrite sym (iter-add{k}{m}{f = L_}{N}) = Distrib-iter
       h2 : toℤ n ≤ℤ mkℤ (suc (k + m)) tt ≡ tt
       h2 rewrite toℤ-+ {suc k} {m} = x
Soundness {mkℤ (suc k) ff} (NatRefl{n}{m} x) = (iter (n + suc k) L_ N , h1 , ≤iterL {n + suc k} {m} h2)
 where h1 : Distrib (suc k) (iter n L_ N) (iter (n + suc k) L_ N)
       h1 rewrite +comm n (suc k)
                | sym (iter-add{k}{n}{f = L_}{N})
               = Distrib-iter
       h2 : n + suc k ≤ m ≡ tt
       h2 rewrite ≤ℤ-+2{toℤ n}{mkℤ (suc k) ff +ℤ toℤ m} (mkℤ (suc k) tt)
                | sym (+ℤ-assoc {mkℤ (suc k) tt}{mkℤ (suc k) ff}{toℤ m})
                | +ℤ-inv {k}
                | toℤ-+ {suc k} {n}
                | sym (suc+ k n)
                = toℤ-≤{n + suc k}{m} h3
                where h3 : toℤ (n + suc k) ≤ℤ toℤ m ≡ tt
                      h3 rewrite +suc n k | +comm n k = x

Soundness (Fun nz jb d d') with Soundness d | Soundness d'
Soundness {mkℤ zero triv} (Fun nz jb d d') | p1 | p2 = {!!}
Soundness {mkℤ (suc k) tt } (Fun nz jb d d') | p1 | p2 = {!!}
Soundness {mkℤ (suc k) ff } (Fun nz jb d d') | p1 | p2 = {!!}
