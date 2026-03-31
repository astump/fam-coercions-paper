module Semantics where

open import lib
open import Tp
open import Declarative
open import Decproc

infix 7 ⟦_⟧ 

⟦_⟧ : Tp! → Tp
⟦ n !N ⟧ = iter n L_ N
⟦ n ! T1 ⇒ T2 ⟧ = iter n L_ (⟦ T1 ⟧ ⇒ ⟦ T2 ⟧)

{- Distrib n T1 T2 means that starting with T1, we can distribute n L's and get T2.
   Distributing an L means putting it either at the start of a type, pushing it
   into domain and codomain, or else pushing it into just the codomain -}
data Distrib : ℕ → Tp → Tp → Set where
  DistribH : ∀{T T' : Tp}{n : ℕ} → 
             Distrib n T T' → 
             Distrib (suc n) T (L T')
  DistribA : ∀{T1 T2 T1' T2' : Tp}{n j : ℕ} → 
              j ≤ n ≡ tt → 
              Distrib j T1 T1' →
              Distrib n T2 T2' →               
              Distrib n (T1 ⇒ T2) (T1' ⇒ T2')
  Distrib0 : ∀{T T' : Tp} →
             T ≡ T' → 
             Distrib 0 T T'

infix 6 ⊨_<_]_

⊨_<_]_ : Tp! → ℤ → Tp! → Set
⊨ T1 < mkℤ 0 triv ] T2 = ⟦ T1 ⟧ <: ⟦ T2 ⟧
⊨ T1 < mkℤ (suc n) tt ] T2 = ∃ Tp (λ T' → Distrib (suc n) ⟦ T2 ⟧ T' ∧ ⟦ T1 ⟧ <: T')
⊨ T1 < mkℤ (suc n) ff ] T2 = ∃ Tp (λ T' → Distrib (suc n) ⟦ T1 ⟧ T' ∧ T' <: ⟦ T2 ⟧ )

Distrib+ : ∀{n x k} →
           Distrib n (iter x L_ N) (iter k L_ N) →
           k ≡ n + x
Distrib+ {n} {zero} {zero} (Distrib0 refl) = refl
Distrib+ {suc n} {zero} {suc k} (DistribH i) rewrite Distrib+{n}{zero}{k} i = refl
Distrib+ {suc n} {suc x} {suc k} (DistribH i) rewrite Distrib+{n}{suc x}{k} i = refl
Distrib+ {zero} {suc x} {suc k} (Distrib0 e) rewrite iterL-inj{suc x}{suc k} e = refl
Distrib+ {zero} {suc x} {zero} (Distrib0 ())

¬Distrib⇒N : ∀{x y z T1 T2} → ¬ Distrib x (iter y L_ (T1 ⇒ T2)) (iter z L_ N)
¬Distrib⇒N {zero} {zero} {zero} (Distrib0 ())
¬Distrib⇒N {zero} {zero} {suc z} (Distrib0 ())
¬Distrib⇒N {zero} {suc y} {zero} (Distrib0 ())
¬Distrib⇒N {zero} {suc y} {suc z} (Distrib0 u) = ⊥-elim (¬⇒iterN{suc y}{suc z} u)
¬Distrib⇒N {suc x} {zero} {suc z} (DistribH i) = ¬Distrib⇒N{x}{zero}{z} i
¬Distrib⇒N {suc x} {suc y} {suc z} (DistribH i) = ¬Distrib⇒N{x}{suc y}{z} i
