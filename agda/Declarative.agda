open import lib
open import Tp

module Declarative where

infix 5 _<:_ 

data _<:_ : Tp → Tp → Set where
  NatRefl : N <: N
  Fun : ∀{T1 T2 T1' T2' : Tp} → 
         T1' <: T1 →
         T2 <: T2' →
         T1 ⇒ T2 <: T1' ⇒ T2'
  Seq : ∀{T1 T2 : Tp} → L (T1 ⇒ T2) <: L T1 ⇒ L T2
  Pure : ∀{T : Tp} → T <: L T
  Cov : ∀{T1 T2 : Tp} → T1 <: T2 → L T1 <: L T2
  Trans : ∀{T1 T2 T3 : Tp} → T1 <: T2 → T2 <: T3 → T1 <: T3

refl-all : ∀{T} → T <: T
refl-all {N} = NatRefl
refl-all {L T} = Cov (refl-all{T})
refl-all {T ⇒ T'} = Fun (refl-all{T}) (refl-all{T'})

fmap : ∀{T1 T2} → T1 ⇒ T2 <: L T1 ⇒ L T2
fmap = Trans Pure Seq

iter-fmap : ∀{k}{T1 T2} → T1 ⇒ T2 <: iter k L_ T1 ⇒ iter k L_ T2
iter-fmap {zero} = refl-all
iter-fmap {suc k} = Trans (iter-fmap{k}) fmap

iter-seq : ∀{k}{T1 T2} → iter k L_ (T1 ⇒ T2) <: iter k L_ T1 ⇒ iter k L_ T2
iter-seq {zero} = refl-all
iter-seq {suc k} = Trans (Cov (iter-seq{k})) Seq

iter-cov : ∀{k}{T1 T2} → T1 <: T2 → iter k L_ T1 <: iter k L_ T2
iter-cov {zero} p = p
iter-cov {suc k} p = Cov (iter-cov{k} p)

iter-pure : ∀{k}{T} → T <: iter k L_ T
iter-pure {zero} = refl-all
iter-pure {suc k} = Trans (iter-pure{k}) Pure

-- compute the size of a derivation
size : ∀{T T' : Tp} → T <: T' → ℕ
size NatRefl = 0
size (Fun d d') = 1 + size d + size d'
size Seq = 0
size Pure = 0
size (Cov d) = 1 + size d
size (Trans d d') = 1 + size d + size d'

≤iterL : ∀{n m : ℕ} → n ≤ m ≡ tt →
         iter n L_ N <: iter m L_ N
≤iterL {zero} {zero} d = NatRefl
≤iterL {zero} {suc m} d = Trans (≤iterL {zero} {m} (0≤{m})) Pure
≤iterL {suc n} {suc m} d = Cov (≤iterL {n} {m} (suc≤{n}{m} d))

≤iterL<: : ∀{n m : ℕ}{T1 T2 : Tp} → n ≤ m ≡ tt →
           T1 <: T2 →
           iter n L_ T1 <: iter m L_ T2
≤iterL<: {zero} {zero} d1 d2 = d2
≤iterL<: {zero} {suc m} d1 d2 = Trans d2 (iter-pure{suc m})
≤iterL<: {suc n} {suc m} d1 d2 = Cov (≤iterL<: {n} {m} (suc≤{n}{m} d1) d2)

≤iterL-all : ∀{n m : ℕ}{T : Tp} → n ≤ m ≡ tt →
             iter n L_ T <: iter m L_ T
≤iterL-all {n} {m} {T} p = ≤iterL<:{n}{m}{T}{T} p (refl-all{T})

N<: : ∀{n T T'} → T ≡ iter n L_ N → T <: T' → ∃ ℕ (λ m → m ≥ n ≡ tt ∧ T' ≡ iter m L_ N)
N<:{zero} e NatRefl = 0 , refl , refl
N<: {zero} {T1 ⇒ T2} {T1' ⇒ T2'} () (Fun d d₁) 
N<: {suc n} {T1 ⇒ T2} {T1' ⇒ T2'} () (Fun d d₁) 
N<: {suc n} e Seq = ⊥-elim (¬⇒iterN{1}{suc n} e)
N<:{n} refl Pure = suc n , ≤-suc n , refl
N<: {suc n} refl (Cov d) with N<:{n} refl d 
N<: {suc n} refl (Cov d) | a , x , refl = suc a , x , refl
N<:{n} e (Trans d d') with N<:{n} e d 
N<:{n} e (Trans d d') | (m , x , e') with N<:{m} e' d' 
N<:{n} e (Trans d d') | (m , x , e') | (m' , y , e'') = m' , ≤-trans{n} x y , e''

<:N : ∀{n T T'} → T' ≡ iter n L_ N → T <: T' → ∃ ℕ (λ m → T ≡ iter m L_ N)
<:N {zero} e NatRefl = 0 , refl
<:N {n} e (Trans d d') with <:N{n} e d'
<:N {n} e (Trans d d') | m , e' = <:N {m} e' d
<:N {suc n}{m} refl Pure = n , refl
<:N {suc n} refl (Cov d) with <:N{n} refl d
<:N {suc n} refl (Cov d) | m , e' = suc m , cong L_ e'

⇒<: : ∀{n T T' T1 T2} → T ≡ iter n L_ (T1 ⇒ T2) → T <: T' →
      ∃ ℕ (λ m → ∃ Tp (λ T1' → ∃ Tp (λ T2' →
      T' ≡ iter m L_ (T1' ⇒ T2'))))
⇒<: {zero} {T1 ⇒ T2} {T'} refl (Fun{T1' = T1'}{T2'} d d₁) = zero , T1' , T2' ,  refl
⇒<: {zero} {T1 ⇒ T2} {T'} refl Pure = 1 , T1 , T2 , refl
⇒<: {zero} {T1 ⇒ T2} {T'} refl (Trans{T2 = T} d d₁) with ⇒<:{zero}{T1 ⇒ T2}{T} refl d
⇒<: {zero} {T1 ⇒ T2} {T'} refl (Trans{T2 = T} d d₁) | m , T1' , T2' , e' with ⇒<:{m}{T}{T'}{T1'}{T2'} e' d₁
⇒<: {zero} {T1 ⇒ T2} {T'} refl (Trans{T2 = T} d d₁) | m , T1' , T2' , e' | k , T1'' , T2'' , b' = k , T1'' , T2'' , b'
⇒<: {suc n} {L (A ⇒ B)} {L A ⇒ L B} {T1} {T2} e Seq = 0 , L A , L B , refl
⇒<: {suc n} {T} {L T} {T1} {T2} e Pure rewrite e = suc (suc n) , T1 , T2 , refl
⇒<: {suc n} {L T} {L T'} {T1} {T2} e (Cov d) with ⇒<:{n}{T}{T'}{T1}{T2} (Linj e) d 
⇒<: {suc n} {L T} {L T'} {T1} {T2} e (Cov d) | k , T1' , T2' , e' = suc k , T1' , T2' , cong L_ e'
⇒<: {suc n} {T} {T'} {T1} {T2} e (Trans{T2 = Tm} d d') with ⇒<:{suc n}{T}{Tm}{T1}{T2} e d
⇒<: {suc n} {T} {T'} {T1} {T2} e (Trans{T2 = Tm} d d') | m , T1' , T2' , e' with ⇒<:{m}{Tm}{T'}{T1'}{T2'} e' d'
⇒<: {suc n} {T} {T'} {T1} {T2} e (Trans{T2 = Tm} d d') | m , T1' , T2' , e' | k , T1'' , T2'' , e'' = k , T1'' , T2'' , e''
