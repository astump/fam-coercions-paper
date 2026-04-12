module Tp where
open import lib

data Tp : Set where
  N : Tp
  L_ : Tp → Tp
  _⇒_ : Tp → Tp → Tp

infixr 9 _⇒_
infixr 10 L_

data Tp! : Set where
  _!N : ℕ → Tp!
  _!_⇒_ : ℕ → Tp! → Tp! → Tp!

infixr 9 _!_⇒_
infixr 10 _!N

¬N⇒ : ∀{n T1 T2} → N ≢ iter n L_ (T1 ⇒ T2)
¬N⇒ {zero} ()
¬N⇒ {suc n} ()

Tp!++ : Tp! → Tp!
Tp!++ (x !N) = suc x !N
Tp!++ (x ! T ⇒ T₁) = suc x ! T ⇒ T₁

Linj : ∀{T T'} → L T ≡ L T' → T ≡ T'
Linj refl = refl

⇒inj : ∀{T1 T2 T1' T2'} → T1 ⇒ T2 ≡ T1' ⇒ T2' → T1 ≡ T1' ∧ T2 ≡ T2'
⇒inj refl = refl , refl

iterLN-inj : ∀{n m : ℕ} → iter n L_ N ≡ iter m L_ N →
            n ≡ m
iterLN-inj {zero} {zero} e = refl
iterLN-inj {suc n} {suc m} e rewrite iterLN-inj{n}{m} (Linj e) = refl

iterL⇒-inj : ∀{n m T1 T2 T1' T2'} → iter n L_ (T1 ⇒ T2) ≡ iter m L_ (T1' ⇒ T2') →
            n ≡ m ∧ T1 ≡ T1' ∧ T2 ≡ T2'
iterL⇒-inj {zero} {zero} refl = refl , refl , refl
iterL⇒-inj {zero} {suc m} ()
iterL⇒-inj {suc n} {zero} ()
iterL⇒-inj {suc n} {suc m} e with iterL⇒-inj{n}{m} (Linj e)
iterL⇒-inj {suc n} {suc m} e | refl , refl , refl = refl , refl , refl

L≢ : ∀{T T' : Tp} → T ≢ T' → L T ≢ L T'
L≢ u refl = u refl

¬⇒iterN : ∀{m n T1 T2} → iter m L_ (T1 ⇒ T2) ≢ iter n L_ N
¬⇒iterN {suc m} {zero} ()
¬⇒iterN {suc m} {suc n} e = L≢ (¬⇒iterN{m}{n}) e 

