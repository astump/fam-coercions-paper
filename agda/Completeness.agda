{- prove completeness of the decision procedure with respect to the
   declarative semantics -}

module Completeness where
open import lib

open import Tp
open import Declarative
open import Decproc
open import DecprocTrans
open import Semantics
open import ExtraIntegerLemmas

{-
Distrib-pure : ∀{n T T'} → 
               Distrib n ⟦ T' ⟧ ⟦ T ⟧ → 
               T < mkℤ (suc n) tt ] T'
Distrib-pure {n} {x !N} {y !N} i rewrite Distrib+{n}{y}{x} i = NatRefl h
 where h : toℤ (n + y) ≤ℤ mkℤ (suc n) tt +ℤ toℤ y ≡ tt
       h rewrite sym (toℤ-+{n}{y}) = ≤ℤ-+1{toℤ n}{mkℤ (suc n) tt}{toℤ y} (≤ℤ-suc{n})

Distrib-pure {n} {x !N} {y ! T' ⇒ T''} i = ⊥-elim (¬Distrib⇒N{n}{y}{x}{⟦ T' ⟧}{⟦ T'' ⟧} i)
Distrib-pure {n} {x ! T' ⇒ T''} {y !N} i = ⊥-elim (¬DistribN⇒{n}{y}{x}{⟦ T' ⟧}{⟦ T'' ⟧} i)
Distrib-pure {n} {x ! T1 ⇒ T2} {y ! T1' ⇒ T2'} i with Distrib⇒{n}{y}{x} i 
Distrib-pure {n} {x ! T1 ⇒ T2} {y ! T1' ⇒ T2'} i | j , jl , i1 , i2 = Fun {!!} {!!} {!!} {!!}
-}

mutual 
 Completeness : ∀{k : ℤ}{T T' : Tp!} → ⊨ T < k ] T' → T < k ] T' 
 Completeness {mkℤ zero triv} {n !N} {m !N} d with N<:{n} refl d
 Completeness {mkℤ zero triv} {n !N} {m !N} d | k , l , e'  = NatRefl h
  where
   h' : n ≤ m ≡ tt
   h' rewrite iterLN-inj{m}{k} e' = l
   h : toℤ n ≤ℤ toℤ m ≡ tt
   h = ≤-toℤ{n}{m} h'
 Completeness {mkℤ zero triv} {n !N} {m ! T' ⇒ T''} d with N<:{n} refl d
 Completeness {mkℤ zero triv} {n !N} {m ! T' ⇒ T''} d | k , _ , e' = ⊥-elim (¬⇒iterN{m}{k} e') 
 Completeness {mkℤ zero triv} {n ! T ⇒ T₁} {m !N} d with <:N{m} refl d
 Completeness {mkℤ zero triv} {n ! T ⇒ T₁} {m !N} d | k , e' = ⊥-elim (¬⇒iterN{n}{k} e')
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {zero ! T' ⇒ T''} (Fun d d') = Fun refl refl (Completeness d) (Completeness d')
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {zero ! T' ⇒ T''} (Trans{T2 = T2} d d') with ⟦⟧inv{T2} 
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {zero ! T' ⇒ T''} (Trans{T2 = T2} d d') | T2' , refl = 
  trns{T2 = T2'}  (Completeness d) (Completeness d')
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {suc m ! T' ⇒ T''} d with keep (iter m L_ (⟦ T' ⟧ ⇒ ⟦ T'' ⟧))
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {suc m ! T' ⇒ T''} d | Ti , e rewrite e with keep (⟦ T ⟧ ⇒ ⟦ T₁ ⟧)
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {suc m ! T' ⇒ T''} d | Ti , e | Ta , e' rewrite e' with d 
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {suc m ! T' ⇒ T''} _ | Ta , e | Ta , e' | Pure = {!!}
 Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {suc m ! T' ⇒ T''} _ | Ti , e | Ta , e' | (Trans d1 d2) = {!!}
 Completeness {mkℤ zero triv} {suc n ! T ⇒ T₁} {zero ! T' ⇒ T''} d = {!!}
 Completeness {mkℤ zero triv} {suc n ! T ⇒ T₁} {suc m ! T' ⇒ T''} d = {!!}
 Completeness {mkℤ (suc n) tt}{T} (T'' , i , d) = pull-Distrib d i
 Completeness {mkℤ (suc n) ff}{T} (T'' , i , d) = pull-Distrib2 d i

 pull-Distrib : ∀{n}{T T' : Tp!}{T'' : Tp} → 
                 ⟦ T ⟧ <: T'' → 
                 Distrib (suc n) T'' ⟦ T' ⟧ → 
                 T < toℤ (suc n) ] T'
 pull-Distrib{n}{T} d i = {!!}

{-
 pull-Distrib : ∀{n}{T T' : Tp!}{T'' : Tp} → 
                 ⟦ T ⟧ <: T'' → 
                 Distrib (suc n) ⟦ T' ⟧ T'' → 
                 T < toℤ (suc n) ] T'
 pull-Distrib {n} {x !N} {y !N} {T''} d i = {!!}
 pull-Distrib {n} {x !N} {y ! T' ⇒ T'''} {T''} d i with N<:{x}{iter x L_ N}{T''} refl d
 pull-Distrib {n} {x !N} {y ! T' ⇒ T'''}  d i | m , _ , refl = ⊥-elim (¬Distrib⇒N{suc n}{y}{m} i)
 pull-Distrib {n} {x ! T ⇒ T₁} {y !N} {T''} d i = {!!}
 pull-Distrib {n} {x ! T ⇒ T₁} {y ! T' ⇒ T'''} {T''} d i = {!!}
-}

 pull-Distrib2 : ∀{n}{T T' : Tp!}{T'' : Tp} → 
                 T'' <: ⟦ T' ⟧ → 
                 Distrib (suc n) ⟦ T ⟧ T'' → 
                 T < mkℤ (suc n) ff ] T'
 pull-Distrib2 = {!!}

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
