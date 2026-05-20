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

⟪_⟫ : Tp → Tp!
⟪ N ⟫ =  0 !N
⟪ L T ⟫ = Tp!++ ⟪ T ⟫
⟪ T1 ⇒ T2 ⟫ = 0 ! ⟪ T1 ⟫ ⇒ ⟪ T2 ⟫

⟦⟧++ : ∀{T : Tp!} → ⟦ Tp!++ T ⟧ ≡ L_ ⟦ T ⟧
⟦⟧++ {x !N} = refl
⟦⟧++ {x ! T ⇒ T₁} = refl

++inv : ∀{T : Tp!}{A : Tp} →
        ⟦ Tp!++ T ⟧ ≡ L A →
        ⟦ T ⟧ ≡ A
++inv {x !N} {A} e = Linj e
++inv {x ! T ⇒ T₁} {A} e = Linj e

⟦⟧inv : ∀{T : Tp} → ∃ Tp! (λ T' → ⟦ T' ⟧ ≡ T)
⟦⟧inv {N} = 0 !N , refl
⟦⟧inv {L_ T} with ⟦⟧inv{T}
⟦⟧inv {L_ T} | T' , refl = Tp!++ T' , ⟦⟧++{T'}
⟦⟧inv {T1 ⇒ T2} with ⟦⟧inv{T1} | ⟦⟧inv{T2} 
⟦⟧inv {T1 ⇒ T2} | T1' , refl | T2' , refl =  0 ! T1' ⇒ T2' , refl

⟦⟧inj : ∀{T1 T2} → ⟦ T1 ⟧ ≡ ⟦ T2 ⟧ → T1 ≡ T2
⟦⟧inj {x !N} {y !N} e rewrite (iterLN-inj{x}{y} e) = refl
⟦⟧inj {x !N} {y ! T2 ⇒ T3} e = ⊥-elim (¬⇒iterN{y}{x} (sym e))
⟦⟧inj {x ! T1 ⇒ T2} {y !N} e = ⊥-elim (¬⇒iterN{x}{y} e)
⟦⟧inj {x ! T1 ⇒ T2} {y ! T3 ⇒ T4} e with iterL⇒-inj{x}{y} e 
⟦⟧inj {x ! T1 ⇒ T2} {y ! T3 ⇒ T4} e | e1 , e2 , e3 rewrite e1 | ⟦⟧inj{T1}{T3} e2 | ⟦⟧inj{T2}{T4} e3 = refl

L≡++ : ∀{T T' : Tp!} →
       ⟦ T ⟧ ≡ L ⟦ T' ⟧ →
       T ≡ Tp!++ T'
L≡++ {x !N} {y !N} e rewrite iterLN-inj{x}{suc y} e = refl
L≡++ {x !N} {y ! T1 ⇒ T2} e = ⊥-elim (¬⇒iterN{suc y}{x} (sym e))
L≡++ {x ! T1 ⇒ T2} {y !N} e = ⊥-elim (¬⇒iterN{x}{suc y} e)
L≡++ {x ! T1 ⇒ T2} {y ! T1' ⇒ T2'} e with iterL⇒-inj{x}{suc y} e 
L≡++ {x ! T1 ⇒ T2} {y ! T1' ⇒ T2'} e | refl , e2 , e3 rewrite ⟦⟧inj{T1}{T1'} e2 | ⟦⟧inj{T2}{T2'} e3 = refl

infix 6 ⊨_<_]_

⊨_<_]_ : Tp! → ℤ → Tp! → Set
⊨ T1 < mkℤ 0 triv ] T2 = ⟦ T1 ⟧ <: ⟦ T2 ⟧
⊨ T1 < mkℤ (suc n) tt ] T2 = ⟦ T1 ⟧ <: iter (suc n) L_ ⟦ T2 ⟧
⊨ T1 < mkℤ (suc n) ff ] T2 = iter (suc n) L_ ⟦ T1 ⟧ <: ⟦ T2 ⟧

iterN⟦⟧ : ∀{n T} → iter n L_ N ≡ ⟦ T ⟧ → T ≡ n !N
iterN⟦⟧ {zero} {zero !N} e = refl
iterN⟦⟧ {suc n} {x !N} e rewrite iterLN-inj{suc n}{x} e = refl
iterN⟦⟧ {n} {x ! T ⇒ T'} e = ⊥-elim (¬⇒iterN{x}{n}{⟦ T ⟧}{⟦ T' ⟧} (sym e))

iter⇒⟦⟧ : ∀{n T Ta Tb} →
          iter n L_ (⟦ Ta ⟧ ⇒ ⟦ Tb ⟧) ≡ ⟦ T ⟧ →
          T ≡ n ! Ta ⇒ Tb
iter⇒⟦⟧ {zero} {x !N} {Ta} {Tb} e = ⊥-elim (¬⇒iterN{0}{x}{⟦ Ta ⟧}{⟦ Tb ⟧} e)
iter⇒⟦⟧ {zero} {zero ! T1 ⇒ T2} {Ta} {Tb} e with iterL⇒-inj{0}{0} e 
iter⇒⟦⟧ {zero} {zero ! T1 ⇒ T2} {Ta} {Tb} e | _ , e1 , e2 rewrite ⟦⟧inj{Ta}{T1} e1 | ⟦⟧inj{Tb}{T2} e2 = refl
iter⇒⟦⟧ {suc n} {suc x !N} {Ta} {Tb} e = ⊥-elim (¬⇒iterN{suc n}{suc x}{⟦ Ta ⟧}{⟦ Tb ⟧} e)
iter⇒⟦⟧ {suc n} {suc x ! T1 ⇒ T2} {Ta} {Tb} e with iterL⇒-inj{suc n}{suc x}{⟦ Ta ⟧}{⟦ Tb ⟧}{⟦ T1 ⟧}{⟦ T2 ⟧} e
iter⇒⟦⟧ {suc n} {suc x ! T1 ⇒ T2} {Ta} {Tb} e | refl , e1 , e2 rewrite ⟦⟧inj{Ta}{T1} e1 | ⟦⟧inj{Tb}{T2} e2 = refl

⟦⟧L : ∀{T : Tp!}{A : Tp} → 
        ⟦ T ⟧ ≡ L A →
        ∃ Tp! (λ A' → T ≡ Tp!++ A')
⟦⟧L {suc x !N} {A} e = x !N , refl
⟦⟧L {suc x ! T1 ⇒ T2} {A} e = x ! T1 ⇒ T2 , refl

iter-Tp!+ : ∀{n : ℕ}{T : Tp!} →
            iter n L_ ⟦ T ⟧ ≡ ⟦ Tp!+ n T ⟧
iter-Tp!+ {k} {x !N} = iter-add{k}
iter-Tp!+ {k} {x ! T ⇒ T₁} = iter-add{k}

