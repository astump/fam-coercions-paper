module Decproc where

open import lib
open import Tp
open import ExtraIntegerLemmas

infix 8 _<_]_ 

data _<_]_ : Tp! → ℤ → Tp! → Set where

 NatRefl : ∀ {n m : ℕ}{k : ℤ} →
          (toℤ n) ≤ℤ k +ℤ (toℤ m) ≡ tt →            -- n ≤ k + m 
          n !N  < k ]  m !N

 Fun : ∀{n m : ℕ}{j k : ℤ}{T1 T2 T1' T2' : Tp!} →
       j ≥ℤ 0ℤ ≡ tt →                               -- j ≥ 0
       j ≥ℤ (toℤ n) -ℤ k -ℤ (toℤ m) ≡ tt →          -- j ≥ n - k - m
       T1'           < j ]       T1  →
       T2            < negℤ j ]  T2' → 
       n ! T1 ⇒ T2   < k ]       m ! T1' ⇒ T2'

refl-decproc : ∀{k : ℤ}{T : Tp!} → k ≥ℤ 0ℤ ≡ tt → T < k ] T
refl-decproc{k}{x !N} e = NatRefl (≤ℤ-+1{0ℤ}{k}{toℤ x} e)
refl-decproc {mkℤ zero triv} {x ! T1 ⇒ T2} e = Fun{j = 0ℤ} refl h (refl-decproc{0ℤ}{T1} refl) (refl-decproc{0ℤ}{T2} refl)
 where h : 0ℤ ≥ℤ ((toℤ x -ℤ mkℤ zero triv) -ℤ toℤ x) ≡ tt
       h rewrite -ℤ-0{toℤ x} | +ℤ-cancel{toℤ x} = refl

refl-decproc {mkℤ (suc n) tt} {x ! T1 ⇒ T2} e =
 Fun{j = 0ℤ} refl h (refl-decproc{0ℤ}{T1} refl) (refl-decproc{0ℤ}{T2} refl)
 where h : 0ℤ ≥ℤ toℤ x -ℤ mkℤ (suc n) tt -ℤ toℤ x ≡ tt
       h rewrite +ℤ-comm{toℤ x}{mkℤ (suc n) ff}
               | +ℤ-assoc{mkℤ (suc n) ff}{toℤ x}{negℤ (toℤ x)}
               | +ℤ-cancel{toℤ x} = refl
refl-decproc {mkℤ (suc n) ff} {x ! T1 ⇒ T2} ()

<]sucN : ∀{x n : ℕ}{T : Tp!} →
         x !N < toℤ n ] T → 
         suc x !N < toℤ (suc n) ] T
<]sucN {x} {n} {y !N} (NatRefl e) = NatRefl h
  where h : mkℤ (suc x) tt ≤ℤ mkℤ (suc n) tt +ℤ toℤ y ≡ tt
        h rewrite suc+ℤ{n}{y} | ≤-≤ℤ{x}{n + y} | toℤ+{n}{y} = e