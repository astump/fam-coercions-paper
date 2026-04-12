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

Tp!++<] : ∀{n : ℕ}{A' T' : Tp!} →
         A' < toℤ n ] T' → 
         Tp!++ A' < mkℤ (suc n) tt ] T'
Tp!++<] {n} (NatRefl {a} {zero} x) rewrite +ℤ-0{toℤ n} = NatRefl (toℤ≤{a} x)
Tp!++<] {n} (NatRefl {a} {suc b} x) rewrite toℤ-+{n}{suc b} = NatRefl (toℤ≤ {a} {n + suc b} x)
Tp!++<] {k} (Fun{n}{m}{j} x x' d d') = Fun{j = j} x h d d'
 where h : j ≥ℤ mkℤ (suc n) tt -ℤ mkℤ (suc k) tt -ℤ toℤ m ≡ tt
       h rewrite suc-ℤsuc{n}{k} = x'

<]Tp!++ : ∀{n : ℕ}{A' T' : Tp!} →
         A' < toℤ- n ] T' → 
         A' < mkℤ (suc n) ff ] Tp!++ T'
<]Tp!++ {zero} (NatRefl {m = zero} x) = NatRefl x
<]Tp!++ {zero} (NatRefl {m = suc m} x) = NatRefl x
<]Tp!++ {suc n} (NatRefl {m = zero} x) = NatRefl x
<]Tp!++ {suc n} (NatRefl {m = suc m} x) = NatRefl x
<]Tp!++ {n} (Fun{n'}{m}{j} x x₁ d d₁) = Fun{j = j} x (h x₁) d d₁
 where h : j ≥ℤ toℤ n' +ℤ negℤ (negℤ (toℤ n)) +ℤ negℤ (toℤ m) ≡ tt →
           j ≥ℤ toℤ n' +ℤ mkℤ (suc n) tt +ℤ mkℤ (suc m) ff ≡ tt
       h u rewrite +ℤ-assoc{toℤ n'}{mkℤ (suc n) tt}{mkℤ (suc m) ff}
         | negℤ-invol{toℤ n}
         | +ℤ-assoc{toℤ n'}{toℤ n}{negℤ (toℤ m)}
         | diffℤ-ℤ{n}{m} = u