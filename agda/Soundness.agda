{- prove soundness of the decision procedure with respect to the
   declarative semantics -}

module Soundness where
open import lib

open import Tp
open import Declarative
open import Decproc
open import Semantics

open import ExtraIntegerLemmas

≤-fun-help : ∀{n m j : ℕ}{T1 T2 T1' T2' : Tp} →
             toℤ n ≤ℤ toℤ j +ℤ toℤ m ≡ tt →
             T1' <: iter j L_ T1 →
             iter j L_ T2 <: T2' →
             iter n L_ (T1 ⇒ T2) <: iter m L_ (T1' ⇒ T2')
≤-fun-help {n} {m} {j} {T1} {T2} {T1'} {T2'} jb p1 p2
  rewrite toℤ-+{j}{m}
        | +comm j m
        = Trans (≤iterL-all{n}{m + j} (toℤ-≤{n}{m + j} jb)) h1
    where h1 : iter (m + j) L_ (T1 ⇒ T2) <: iter m L_ (T1' ⇒ T2')
          h1 rewrite sym (iter-add{m}{j}{f = L_}{x = T1 ⇒ T2})
             = iter-cov {m} (Trans (iter-seq{j}) (Fun p1 p2))


Soundness : ∀{k : ℤ}{T T' : Tp!} → T < k ] T' → ⊨ T < k ] T'
Soundness {mkℤ zero triv} (NatRefl{n}{m} x) with toℤ-≤{n}{m} x 
Soundness {mkℤ zero triv} (NatRefl{n}{m} x) | u = ≤iterL{n}{m} u
Soundness {mkℤ (suc k) tt} (NatRefl{n}{m} x)
  rewrite iter-add{k}{m}{f = L_}{x = N}
        | toℤ-+{suc k}{m}
        = ≤iterL {n} (toℤ-≤{n} x)
Soundness {mkℤ (suc k) ff} (NatRefl{n}{m} x)
  rewrite iter-add{k}{n}{f = L_}{x = N}
        | ≤ℤ-+2{toℤ n}{mkℤ (suc k) ff +ℤ toℤ m} (toℤ (suc k))
        | sym (+ℤ-assoc{toℤ (suc k)}{mkℤ (suc k) ff}{toℤ m})
        | diffℤ-nn{k}
        | toℤ-+{suc k}{n}
        = ≤iterL {suc (k + n)} {m} (toℤ-≤{suc (k + n)}{m} x)

Soundness (Fun nz jb d d') with Soundness d | Soundness d'
Soundness
  {mkℤ zero triv}
  (Fun {n} {m} {j = mkℤ zero triv} nz jb x y)
  | p1 | p2
  rewrite +ℤ-0{toℤ n}
        | ≤ℤ-subℤ2 {toℤ n} {toℤ m} {0ℤ}
        = ≤iterL<: {n} (toℤ-≤ {n} jb) (Fun p1 p2)
Soundness
  {mkℤ zero triv}
  (Fun {n} {m} {mkℤ (suc j) tt} {k} {T1} {T2} {T1'} {T2'} nz jb x y)
  | p1 | p2
  rewrite +ℤ-0 {toℤ n}
        | ≤ℤ-subℤ2 {toℤ n} {toℤ m} {toℤ (suc j)}
        = ≤-fun-help {n} {m} {suc j} jb p1 p2

Soundness
  {mkℤ (suc k) tt}
  (Fun {n} {m} {mkℤ zero triv} {k'} {T1} {T2} {T1'} {T2'} nz jb x y)
  | p1 | p2
  rewrite ≤ℤ-subℤ2 {toℤ n +ℤ mkℤ (suc k) ff} {toℤ m} {0ℤ}
        | ≤ℤ-subℤ2 {toℤ n} {toℤ (suc k)} {toℤ m}
        | +ℤ-comm {toℤ m} {toℤ (suc k)}
        | sym (toℤ+{suc k}{m})
        | iter-add{suc k}{m}{f = L_}{x = ⟦ T1' ⟧ ⇒ ⟦ T2' ⟧}
        = ≤iterL<:{n} (toℤ-≤ {n} jb) (Fun p1 p2)
Soundness
  {mkℤ (suc k) tt}
  (Fun {n} {m} {mkℤ (suc j) tt} {k'} {T1} {T2} {T1'} {T2'} nz jb x y)
  | p1 | p2
  rewrite iter-add{suc k}{m}{f = L_}{x = ⟦ T1' ⟧ ⇒ ⟦ T2' ⟧}
        | ≤ℤ-subℤ2 {toℤ n +ℤ mkℤ (suc k) ff}{toℤ m}{toℤ (suc j)}
        | ≤ℤ-subℤ2 {toℤ n}{toℤ (suc k)}{toℤ (suc j) +ℤ toℤ m}
        | +ℤ-assoc{toℤ (suc j)}{toℤ m}{toℤ (suc k)}
        | sym (toℤ+ {m} {suc k})
        | +comm m (suc k)
        = ≤-fun-help{n}{suc k + m}{suc j} jb p1 p2

Soundness
  {mkℤ (suc k) ff}
  (Fun {n} {m} {mkℤ zero triv} {k'} {T1} {T2} {T1'} {T2'} nz jb x y)
  | p1 | p2
  rewrite ≤ℤ-subℤ2 {toℤ n +ℤ toℤ (suc k)} {toℤ m} {0ℤ}
        | +ℤ-comm {toℤ n} {toℤ (suc k)}
        | sym (toℤ+{suc k}{n})
        | iter-add{suc k}{n}{f = L_}{x = ⟦ T1 ⟧ ⇒ ⟦ T2 ⟧}
        = ≤iterL<:{suc (k + n)}{m} (toℤ-≤ {suc (k + n)}{m} jb) (Fun p1 p2)
Soundness
  {mkℤ (suc k) ff}
  (Fun {n} {m} {mkℤ (suc j) tt} {k'} {T1} {T2} {T1'} {T2'} nz jb x y)
  | p1 | p2
  rewrite ≤ℤ-subℤ2 {toℤ n +ℤ toℤ (suc k)} {toℤ m} {toℤ (suc j)}
        | sym (toℤ+ {n} {suc k})
        | +comm n (suc k)
        | iter-add{suc k}{n}{f = L_}{x = ⟦ T1 ⟧ ⇒ ⟦ T2 ⟧}
        = ≤-fun-help {suc k + n} {m} {suc j} jb p1 p2

Soundness (Fun {j = mkℤ (suc j) ff} nz jb x y) | p1 | p2 with nz
Soundness (Fun {j = mkℤ (suc j) ff} nz jb x y) | p1 | p2 | ()
