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

infix 6 ⊨_<_]_

⊨_<_]_ : Tp! → ℤ → Tp! → Set
⊨_<_]_ T1 (mkℤ 0 triv) T2 = ⟦ T1 ⟧ <: ⟦ T2 ⟧
⊨_<_]_ T1 (mkℤ (suc n) tt) T2 = ∃ Tp (λ T' → Distrib (suc n) ⟦ T2 ⟧ T' ∧ ⟦ T1 ⟧ <: T')
⊨_<_]_ T1 (mkℤ (suc n) ff) T2 = ∃ Tp (λ T' → Distrib (suc n) ⟦ T1 ⟧ T' ∧ T' <: ⟦ T2 ⟧ )