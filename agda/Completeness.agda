{- prove completeness of the decision procedure with respect to the
   declarative semantics -}

module Completeness where
open import lib

open import Tp
open import Declarative
open import Decproc
open import Semantics

mutual 
 Completeness : ∀{k : ℤ}{T T' : Tp!} → ⊨ T < k ] T' → T < k ] T' 
 Completeness {mkℤ zero triv} {n !N} {m !N} d with N<:{n} refl d
 Completeness {mkℤ zero triv} {n !N} {m !N} d | k , l , e'  = NatRefl h
  where
   h' : n ≤ m ≡ tt
   h' rewrite iterL-inj{m}{k} e' = l
   h : toℤ n ≤ℤ toℤ m ≡ tt
   h = ≤-toℤ{n}{m} h'
 Completeness {mkℤ zero triv} {n !N} {m ! T' ⇒ T''} d with N<:{n} refl d
 Completeness {mkℤ zero triv} {n !N} {m ! T' ⇒ T''} d | k , _ , e' = ⊥-elim (¬⇒iterN{m}{k} e') 
 Completeness {mkℤ zero triv} {n ! T ⇒ T₁} {m !N} d with <:N{m} refl d
 Completeness {mkℤ zero triv} {n ! T ⇒ T₁} {m !N} d | k , e' = ⊥-elim (¬⇒iterN{n}{k} e')
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {zero ! T' ⇒ T''} (Fun d d') = Fun refl refl (Completeness d) (Completeness d')
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {zero ! T' ⇒ T''} (Trans d d') = {!!}
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {suc m ! T' ⇒ T''} d = {!!}
 Completeness {mkℤ zero triv} {suc n ! T ⇒ T₁} {zero ! T' ⇒ T''} d = {!!}
 Completeness {mkℤ zero triv} {suc n ! T ⇒ T₁} {suc m ! T' ⇒ T''} d = {!!}
 Completeness {mkℤ (suc n) tt}{T} (T'' , i , d) = {!!}
 Completeness {mkℤ (suc n) ff}{T} (T'' , i , d) = {!!}

 pull-Distrib : ∀{n}{T T' : Tp!}{T'' : Tp} → 
                 ⟦ T ⟧ <: T'' → 
                 Distrib (suc n) ⟦ T' ⟧ T'' → 
                 T < toℤ (suc n) ] T'
 pull-Distrib {n} {m !N} {T'} {T''} d i with N<:{m} refl d
 pull-Distrib {n} {m !N} {x !N} {_} d i | k , le , refl rewrite Distrib+{suc n}{x}{k} i = NatRefl h
  where h : toℤ m ≤ℤ toℤ (suc n) +ℤ toℤ x ≡ tt
        h rewrite sym (toℤ+{suc n}{x}) = ≤-toℤ{m} le
 pull-Distrib {n} {m !N} {x ! T' ⇒ T''} {_} d i | k , le , refl = ⊥-elim (¬Distrib⇒N{suc n}{x}{k} i)
 pull-Distrib {n} {zero ! T ⇒ T₁} {T'} {T''} (Fun d d₁) i = {!!}
 pull-Distrib {n} {zero ! T ⇒ T₁} {T'} {T''} Pure i = {!!}
 pull-Distrib {n} {zero ! T ⇒ T₁} {T'} {T''} (Trans d d₁) i = {!!}
 pull-Distrib {n} {suc x ! T ⇒ T₁} {T'} {T''} d i = {!!}

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
