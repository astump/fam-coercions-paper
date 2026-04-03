module Semantics where

open import lib
open import Tp
open import Declarative
open import Decproc
open import ExtraIntegerLemmas

infix 7 ⟦_⟧ 

⟦_⟧ : Tp! → Tp
⟦ n !N ⟧ = iter n L_ N
⟦ n ! T1 ⇒ T2 ⟧ = iter n L_ (⟦ T1 ⟧ ⇒ ⟦ T2 ⟧)

⟦⟧++ : ∀{T : Tp!} → ⟦ Tp!++ T ⟧ ≡ L ⟦ T ⟧
⟦⟧++ {x !N} = refl
⟦⟧++ {x ! T ⇒ T₁} = refl

⟦⟧inv : ∀{T : Tp} → ∃ Tp! (λ T' → ⟦ T' ⟧ ≡ T)
⟦⟧inv {N} = 0 !N , refl
⟦⟧inv {L T} with ⟦⟧inv{T}
⟦⟧inv {L T} | T' , refl = Tp!++ T' , ⟦⟧++{T'}
⟦⟧inv {T1 ⇒ T2} with ⟦⟧inv{T1} | ⟦⟧inv{T2} 
⟦⟧inv {T1 ⇒ T2} | T1' , refl | T2' , refl =  0 ! T1' ⇒ T2' , refl

⟦⟧inj : ∀{T1 T2} → ⟦ T1 ⟧ ≡ ⟦ T2 ⟧ → T1 ≡ T2
⟦⟧inj {x !N} {y !N} e rewrite (iterLN-inj{x}{y} e) = refl
⟦⟧inj {x !N} {y ! T2 ⇒ T3} e = ⊥-elim (¬⇒iterN{y}{x} (sym e))
⟦⟧inj {x ! T1 ⇒ T2} {y !N} e = ⊥-elim (¬⇒iterN{x}{y} e)
⟦⟧inj {x ! T1 ⇒ T2} {y ! T3 ⇒ T4} e with iterL⇒-inj{x}{y} e 
⟦⟧inj {x ! T1 ⇒ T2} {y ! T3 ⇒ T4} e | e1 , e2 , e3 rewrite e1 | ⟦⟧inj{T1}{T3} e2 | ⟦⟧inj{T2}{T4} e3 = refl

{- Distrib n T1 T2 means that starting with T1, we can distribute n L's and get T2.
   Distributing an L means putting it either at the start of a type, pushing it
   into domain and codomain, or else pushing it into just the codomain -}
data Distrib : ℕ → Tp → Tp → Set where
  DistribH : ∀{T T' : Tp}{n : ℕ} → 
             Distrib n T T' → 
             Distrib (suc n) T (L T')
  DistribA : ∀{T1 T2 T1' T2' : Tp}{n j : ℕ} → 
              j ≤ suc n ≡ tt → 
              Distrib j T1 T1' →
              Distrib (suc n) T2 T2' →               
              Distrib (suc n) (T1 ⇒ T2) (T1' ⇒ T2')
  DistribL : ∀{T T' : Tp}{n : ℕ} →
             Distrib n T T' →
             Distrib n (L T) (L T')
  Distrib0 : ∀{T T' : Tp} →
             T ≡ T' → 
             Distrib 0 T T'

infix 6 ⊨_<_]_

⊨_<_]_ : Tp! → ℤ → Tp! → Set
⊨ T1 < mkℤ 0 triv ] T2 = ⟦ T1 ⟧ <: ⟦ T2 ⟧
⊨ T1 < mkℤ (suc n) tt ] T2 = ∃ Tp (λ T' → Distrib (suc n) T' ⟦ T2 ⟧ ∧ ⟦ T1 ⟧ <: T')
⊨ T1 < mkℤ (suc n) ff ] T2 = ∃ Tp (λ T' → Distrib (suc n) ⟦ T1 ⟧ T' ∧ T' <: ⟦ T2 ⟧ )

Distrib+ : ∀{n x k} →
           Distrib n (iter x L_ N) (iter k L_ N) →
           k ≡ n + x
Distrib+ {n} {zero} {zero} (Distrib0 refl) = refl
Distrib+ {suc n} {zero} {suc k} (DistribH i) rewrite Distrib+{n}{zero}{k} i = refl
Distrib+ {suc n} {suc x} {suc k} (DistribH i) rewrite Distrib+{n}{suc x}{k} i = refl
Distrib+ {zero} {suc x} {suc k} (Distrib0 e) rewrite iterLN-inj{suc x}{suc k} e = refl
Distrib+ {zero} {suc x} {zero} (Distrib0 ())
Distrib+ {n}{suc x}{suc k} (DistribL i) rewrite Distrib+{n}{x}{k} i | +suc n x = refl

¬Distrib⇒N : ∀{x y z T1 T2} → ¬ Distrib x (iter y L_ (T1 ⇒ T2)) (iter z L_ N)
¬Distrib⇒N {zero} {zero} {zero} (Distrib0 ())
¬Distrib⇒N {zero} {zero} {suc z} (Distrib0 ())
¬Distrib⇒N {zero} {suc y} {zero} (Distrib0 ())
¬Distrib⇒N {zero} {suc y} {suc z} (Distrib0 u) = ¬⇒iterN{suc y}{suc z} u
¬Distrib⇒N {suc x} {zero} {suc z} (DistribH i) = ¬Distrib⇒N{x}{zero}{z} i
¬Distrib⇒N {suc x} {suc y} {suc z} (DistribH i) = ¬Distrib⇒N{x}{suc y}{z} i
¬Distrib⇒N {n}{suc x}{suc k} (DistribL i) = ¬Distrib⇒N{n}{x}{k} i

¬DistribN⇒ : ∀{x y z T1 T2} → ¬ Distrib x (iter y L_ N) (iter z L_ (T1 ⇒ T2))
¬DistribN⇒ {zero} {zero} {zero} (Distrib0 ())
¬DistribN⇒ {zero} {zero} {suc z} (Distrib0 ())
¬DistribN⇒ {zero} {suc y} {zero} (Distrib0 ())
¬DistribN⇒ {zero} {suc y} {suc z}{T1}{T2} (Distrib0 e) = ¬⇒iterN{suc z}{suc y} (sym e)
¬DistribN⇒ {suc x} {zero} {suc z} (DistribH i) = ¬DistribN⇒{x}{zero}{z} i
¬DistribN⇒ {suc x} {suc y} {suc z} (DistribH i) = ¬DistribN⇒{x}{suc y}{z} i
¬DistribN⇒ {n}{suc x}{suc k} (DistribL i) = ¬DistribN⇒{n}{x}{k} i

Distrib⇒ : ∀{n x y T1 T2 T1' T2'} →
           Distrib n (iter x L_ (T1 ⇒ T2))
                     (iter y L_ (T1' ⇒ T2')) →
           let n' = n + x ∸ y in
            ∃ ℕ (λ j → j ≤ n' ≡ tt ∧
                 Distrib j T1 T1' ∧ 
                 Distrib n' T2 T2')
Distrib⇒ {suc n} {zero} {zero} (DistribA{j = j} x i i') rewrite +0 n = j , x , i , i'
Distrib⇒ {n} {zero} {zero} (Distrib0 refl) = 0 , refl , Distrib0 refl , Distrib0 refl
Distrib⇒ {suc n} {zero} {suc y} (DistribH i) = Distrib⇒{n}{zero}{y} i 
Distrib⇒ {n} {suc x} {zero} (Distrib0 ())
Distrib⇒ {suc n} {suc x} {suc y} (DistribH i) = Distrib⇒{n}{suc x}{y} i
Distrib⇒ {n} {suc x} {suc y} (DistribL i) with Distrib⇒{n}{x}{y} i
Distrib⇒ {n} {suc x} {suc y} (DistribL i) | j , jl , i1 , i2 rewrite +suc n x = j , jl , i1 , i2
Distrib⇒ {0} {suc x} {suc y} (Distrib0 e) with iterL⇒-inj{suc x}{suc y} e 
Distrib⇒ {0} {suc x} {suc y} (Distrib0 e) | refl , e2 , e3 rewrite ∸cancel1 x = 0 , refl , Distrib0 e2 , Distrib0 e3

{-
mutual 
 Distrib< : ∀{n T1 T2} → 
            Distrib n ⟦ T1 ⟧ ⟦ T2 ⟧ →
            T1 < toℤ n ] T2
 Distrib< {n} {x !N} {x₁ !N} i = NatRefl {!!}
 Distrib< {n} {x !N} {x₁ ! T2 ⇒ T3} i = {!!}
 Distrib< {n} {x ! T1 ⇒ T2} {x₁ !N} i = {!!}
 Distrib< {n} {x ! T1 ⇒ T2} {y ! T1' ⇒ T2'} i with Distrib⇒{n}{x}{y}{⟦ T1 ⟧}{⟦ T2 ⟧}{⟦ T1' ⟧}{⟦ T2' ⟧} i 
 Distrib< {n} {x ! T1 ⇒ T2} {y ! T1' ⇒ T2'} i | j , jl , i1 , i2 = Fun {!!} {!!} (Distrib<- i1) {!!}

 Distrib<- : ∀{n T1 T2} → 
             Distrib n ⟦ T1 ⟧ ⟦ T2 ⟧ →
             T2 < toℤ- n ] T1
 Distrib<-{n}{T1}{T2} i = {!!}
 -}