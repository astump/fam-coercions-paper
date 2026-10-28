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

Clem1 : ∀{a : ℕ} → toℤ (suc a) ≤ℤ mkℤ 1 tt +ℤ toℤ a ≡ tt
Clem1{a} rewrite (+1ℤa{a}) = ≤ℤ-refl{mkℤ 1 tt +ℤ toℤ a}

Clem2 : ∀{b : ℕ} → toℤ b ≤ℤ diffℤ b 0 ≡ tt
Clem2{b} rewrite diffℤ-0{b} = ≤ℤ-refl{toℤ b}

Clem3 : ∀{a : ℕ}{T1 : Tp!} → L iter a L_ N ≡ L ⟦ T1 ⟧ →
        suc a !N < mkℤ 1 tt ] T1
Clem3{a}{T1} e rewrite iterN⟦⟧{a}{T1} (Linj e) = NatRefl (Clem1{a})        

Clem4 : ∀{b : ℕ}{T2 : Tp!} → 
        L iter b L_ N ≡ L ⟦ T2 ⟧ → 
        T2 < mkℤ 1 ff ] suc b !N
Clem4{b}{T2} e rewrite iterN⟦⟧{b}{T2} (Linj e) = NatRefl (Clem2{b})

Clem5 : ∀{b : ℕ}{T2 T2a T2b : Tp!} →
        L iter b L_ (⟦ T2a ⟧ ⇒ ⟦ T2b ⟧) ≡ L ⟦ T2 ⟧ →
        T2 < mkℤ 1 ff ] suc b ! T2a ⇒ T2b
Clem5{b}{T2}{T2a}{T2b} e rewrite iter⇒⟦⟧{b}{T2}{T2a}{T2b} (Linj e) = Fun{j = 0ℤ} refl h (refl-decproc refl) (refl-decproc refl)
 where h : 0ℤ ≥ℤ toℤ b +ℤ 1ℤ +ℤ mkℤ (suc b) ff ≡ tt
       h rewrite sym (+1ℤ{b}) rewrite diffℤ-nn{b} = refl

Clem6 : ∀{a : ℕ}{T1 T1a T1b : Tp!} →
        L iter a L_ (⟦ T1a ⟧ ⇒ ⟦ T1b ⟧) ≡ L ⟦ T1 ⟧ →
        suc a ! T1a ⇒ T1b < 1ℤ ] T1
Clem6{a}{T1}{T1a}{T1b} e rewrite iter⇒⟦⟧{a}{T1}{T1a}{T1b} (Linj e) = Fun{j = 0ℤ} refl h (refl-decproc refl) (refl-decproc refl)
 where h : 0ℤ ≥ℤ toℤ (suc a) +ℤ mkℤ 1 ff -ℤ toℤ a ≡ tt
       h rewrite diffℤ-0{a} | +ℤ-cancel{toℤ a} = refl

Clem7a : ∀{y : ℕ} → diffℤ y 1 +ℤ negℤ (toℤ y) ≡ -1ℤ
Clem7a {zero} = refl
Clem7a {suc y} rewrite diffℤ-0{y} = -ℤ-suc{y}

Clem7 : ∀{n : ℕ}{T T' : Tp!} →
        iter n L_ ⟦ T' ⟧ ≡ ⟦ T ⟧ →
        T < toℤ (suc n) ] T'
Clem7 {zero} {T} {T'} e rewrite ⟦⟧inj{T'}{T} e = refl-decproc{1ℤ} refl
Clem7 {suc n} {suc x !N} {T'} e = <]sucN (Clem7{n}{x !N}{T'} (Linj e))
Clem7 {suc n} {x ! T ⇒ T₁} {y !N} e rewrite iter-add{n}{y}{f = L_}{N} = ⊥-elim (¬⇒iterN{x}{suc n + y} (sym e))
Clem7 {suc n} {x ! T ⇒ T₁} {y ! T' ⇒ T''} e rewrite iter-add{n}{y}{f = L_}{⟦ T' ⟧ ⇒ ⟦ T'' ⟧}
 with iterL⇒-inj{suc n + y}{x}{⟦ T' ⟧}{⟦ T'' ⟧}{⟦ T ⟧}{⟦ T₁ ⟧} e 
Clem7 {suc n} {_ ! T ⇒ T₁} {y ! T' ⇒ T''} e | refl , e2 , e3 rewrite ⟦⟧inj{T''}{T₁} e3 | ⟦⟧inj{T'}{T} e2 =
  Fun{j = 0ℤ} refl h (refl-decproc refl) (refl-decproc refl)
  where h : 0ℤ ≥ℤ mkℤ (suc (n + y)) tt -ℤ mkℤ (suc (suc n)) tt -ℤ toℤ y ≡ tt
        h rewrite diffℤ-+suc{n}{y} rewrite Clem7a{y} = refl

Clem8 : ∀{x y : ℕ}{T1 T2 T1' T2' : Tp!} →
        x ! T1 ⇒ T2 < 0ℤ ] y ! T1' ⇒ T2' →
        suc x ! T1 ⇒ T2 < mkℤ 0 triv ] suc y ! T1' ⇒ T2'
Clem8{x}{y} (Fun{j = j} u v d1 d2) = Fun{j = j} u h d1 d2
  where h : j ≥ℤ mkℤ (suc x) tt -ℤ mkℤ (suc y) tt ≡ tt
        h rewrite suc-ℤsuc{x}{y} | +ℤ-0{toℤ x} = v 

Clem11 : ∀{A B : Tp!} →
         0 ! A ⇒ B < mkℤ 1 ff ] 0 ! Tp!++ A ⇒ Tp!++ B
Clem11 = Fun{j = 1ℤ} refl refl (Tp!++<] (refl-decproc {0ℤ} refl)) (<]Tp!++ (refl-decproc{0ℤ} refl))

Clem12 : ∀{n : ℕ}{T A'' : Tp!} →
          iter n L_ ⟦ T ⟧ ≡ ⟦ A'' ⟧ → 
          T < toℤ- n ] Tp!++ A''
Clem12 {zero} {T} {x !N} e rewrite iterN⟦⟧{x}{T} (sym e) = NatRefl (≤ℤ-suc{x}{tt})
Clem12 {zero} {T} {x ! A'' ⇒ A'''} e rewrite iter⇒⟦⟧{x}{T}{A''}{A'''} (sym e) = Fun{j = 0ℤ} refl h (refl-decproc refl) (refl-decproc refl)
 where h : 0ℤ ≥ℤ toℤ x +ℤ mkℤ 0 triv +ℤ mkℤ (suc x) ff ≡ tt
       h rewrite +ℤ-0{toℤ x} | -ℤ-suc{x} = refl
Clem12 {suc n} {T} {A''} e with ⟦⟧L{A''}{iter n L_ ⟦ T ⟧} (sym e) 
Clem12 {suc n} {T}  e | M , refl = <]Tp!++ (Clem12 (sym (++inv{M}{iter n L_ ⟦ T ⟧} (sym e)))) 

Completeness : ∀{k : ℤ}{T T' : Tp!} → ⊨ T < k ] T' → T < k ] T' 
Completeness {mkℤ zero triv} {x !N} {y !N} d with N<:{x}{iter x L_ N}{iter y L_ N} refl d
Completeness {mkℤ zero triv} {x !N} {y !N} d | m , lm , e rewrite iterLN-inj{y}{m} e = NatRefl (≤-≤ℤ1{x} lm)
Completeness {mkℤ zero triv} {x !N} {y ! T' ⇒ T''} d with N<:{x} refl d 
Completeness {mkℤ zero triv} {x !N} {y ! T' ⇒ T''} d | m , lm , e = ⊥-elim (¬⇒iterN{y}{m} e)
Completeness {mkℤ zero triv} {x ! T ⇒ T₁} {y !N} d with <:N{y} refl d
Completeness {mkℤ zero triv} {x ! T ⇒ T₁} {y !N} d | m  , e = ⊥-elim (¬⇒iterN{x}{m} e) 
Completeness {mkℤ zero triv} {zero ! T ⇒ T₁} {zero ! T' ⇒ T''} (Fun d d') = Fun{j = 0ℤ} refl refl (Completeness d) (Completeness d')
Completeness {mkℤ zero triv} {zero ! T1 ⇒ T2} {zero ! T1' ⇒ T2'} (Trans{T2 = TM} d d') with ⟦⟧inv{TM} 
Completeness {mkℤ zero triv} {zero ! T1 ⇒ T2} {zero ! T1' ⇒ T2'} (Trans{T2 = TM} d d') | TM' , refl =
  trns (Completeness {0ℤ} d) (Completeness{0ℤ}{TM'} d') 
Completeness {mkℤ zero triv} {zero ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} d with keep (⟦ T1 ⟧ ⇒ ⟦ T2 ⟧) 
Completeness {mkℤ zero triv} {zero ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} d | TL , e rewrite e with d 
Completeness {mkℤ zero triv} {zero ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} d | _ , e | Pure with iterL⇒-inj{0}{y} e
Completeness {mkℤ zero triv} {zero ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} d | _ , e | Pure | refl , e2 , e3 = 
  Fun{j = 0ℤ} refl refl h1 h2
  where h1 : T1' < 0ℤ ] T1
        h1 rewrite ⟦⟧inj{T1}{T1'} e2 = refl-decproc refl
        h2 : T2 < 0ℤ ] T2'
        h2 rewrite ⟦⟧inj{T2}{T2'} e3 = refl-decproc refl
Completeness {mkℤ zero triv} {zero ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} d | TL , e | Trans{T2 = TM} d1 d2 with ⟦⟧inv{TM}
Completeness {mkℤ zero triv} {zero ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} d | TL , e | Trans{T2 = _} d1 d2 | TM' , refl rewrite sym e =
  trns {0 ! T1 ⇒ T2} {TM'} {suc y ! T1' ⇒ T2'} (Completeness{0ℤ}{0 ! T1 ⇒ T2} d1) (Completeness{0ℤ}{TM'}{suc y ! T1' ⇒ T2'} d2)
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {zero ! T1' ⇒ T2'} d with keep (iter x L_ (⟦ T1 ⟧ ⇒ ⟦ T2 ⟧)) | keep ⟦ T1' ⟧ | keep ⟦ T2' ⟧
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {zero ! T1' ⇒ T2'} d | Ta , e | T1a , e1 | T2a , e2 rewrite e | e1 | e2 with d 
Completeness {mkℤ zero triv} {1 ! T1 ⇒ T2} {zero ! (suc a !N) ⇒ (suc b !N)} _ | _ , refl | _ , e1 | _ , e2 | Seq =
  Fun{j = toℤ 1} refl refl (Clem3{a}{T1} e1)  (Clem4{b}{T2} e2) 
Completeness {mkℤ zero triv} {1 ! T1 ⇒ T2} {zero ! (suc a !N) ⇒ (suc b ! T2a ⇒ T2b)} _ | _ , refl | _ , e1 | _ , e2 | Seq = 
  Fun{j = toℤ 1} refl refl (Clem3{a}{T1} e1) (Clem5{b}{T2}{T2a}{T2b} e2)

Completeness {mkℤ zero triv} {1 ! T1 ⇒ T2} {zero ! (suc a ! T1a ⇒ T1b) ⇒ (suc b !N)} _ | _ , refl | _ , e1 | _ , e2 | Seq =
  Fun refl refl (Clem6 e1) (Clem4 e2)
Completeness {mkℤ zero triv} {1 ! T1 ⇒ T2} {zero ! (suc a ! T1a ⇒ T1b) ⇒ (suc b ! T2a ⇒ T2b)} _ | _ , refl | _ , e1 | _ , e2 | Seq = 
  Fun{j = 1ℤ} refl refl (Clem6 e1) (Clem5 e2)
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {zero ! T1' ⇒ T2'} _ | _ , refl | T1a , e1 | T2a , e2 | Trans{T2 = T3} d1 d2
  with ⟦⟧inv{T3}
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {zero ! T1' ⇒ T2'} _ | _ , refl | _ , refl | _ , refl | Trans d1 d2 | T3' , refl =
 trns (Completeness {0ℤ} {suc x ! T1 ⇒ T2} {T3'} d1) (Completeness{0ℤ}{T3'}{0 ! T1' ⇒ T2'} d2)
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} d with keep (iter y L_ (⟦ T1' ⟧ ⇒ ⟦ T2' ⟧))
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} d | M , e rewrite e with d 
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} _ | _ , e | Pure 
 with iterL⇒-inj{y}{suc x}{⟦ T1' ⟧}{⟦ T2' ⟧}{⟦ T1 ⟧}{⟦ T2 ⟧} e
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} _ | _ , e | Pure | refl , e2 , e3
  rewrite ⟦⟧inj{T2'}{T2} e3 | ⟦⟧inj{T1'}{T1} e2 =
  Fun{j = 0ℤ} refl h (refl-decproc refl) (refl-decproc refl)
  where h : 0ℤ ≥ℤ mkℤ (suc x) tt +ℤ mkℤ 0 triv -ℤ mkℤ (suc (suc x)) tt ≡ tt
        h rewrite +ℤ0{mkℤ (suc x) tt} | diffℤ-1{x} = refl
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} _ | _ , refl | Cov d =
  Clem8 (Completeness{0ℤ}{x ! T1 ⇒ T2}{y ! T1' ⇒ T2'} d)
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} _ | M , e | Trans{T2 = T3} d1 d2 with ⟦⟧inv{T3} 
Completeness {mkℤ zero triv} {suc x ! T1 ⇒ T2} {suc y ! T1' ⇒ T2'} _ | _ , refl | Trans d1 d2 | a , refl =
  trns (Completeness{0ℤ}{suc x ! T1 ⇒ T2}{a} d1) (Completeness d2)
Completeness {mkℤ (suc n) tt} {T} {T'} d with keep (⟦ T ⟧) | keep (iter n L_ ⟦ T' ⟧)
Completeness {mkℤ (suc n) tt} {T} {T'} d | A , e | B , e' rewrite e | e' with d 
Completeness {mkℤ (suc n) tt} {T} {T'} _ | A , e | _ , e' | Pure rewrite sym e = Clem7 e'
Completeness {mkℤ (suc n) tt} {T} {T'} _ | L A , e | _ , refl | Cov d with ⟦⟧L{T}{A} e
Completeness {mkℤ (suc n) tt} {_} {T'} _ | L A , e | _ , refl | Cov d | A' , refl with ++inv{A'}{A} e 
Completeness {mkℤ (suc zero) tt} {_} {T'} _ | L _ , e | _ , refl | Cov d | A' , refl | refl = Tp!++<] (Completeness{0ℤ} d)
Completeness {mkℤ (suc (suc n)) tt} {_} {T'} _ | L _ , e | _ , refl | Cov d | A' , refl | refl = Tp!++<] (Completeness{toℤ (suc n)} d)
Completeness {mkℤ (suc n) tt} {T} {T'} _ | _ , refl | _ , refl | Trans{T2 = T2} d1 d2 with ⟦⟧inv{T2} 
Completeness {mkℤ (suc n) tt} {T} {T'} _ | _ , refl | _ , refl | Trans d1 d2 | A , refl =
  trns{T2 = A} (Completeness{0ℤ} d1) (Completeness{toℤ (suc n)} d2)
Completeness {mkℤ (suc n) ff} {T} {T'} d with keep (iter n L_ ⟦ T ⟧) | keep ⟦ T' ⟧
Completeness {mkℤ (suc n) ff} {T} {T'} d | A , e | B , e' rewrite e | e' with d 
Completeness {mkℤ (suc n) ff} {T} {0 !N} _ | _ , e | _ , () | Seq
Completeness {mkℤ (suc n) ff} {T} {suc x !N} _ | _ , e | _ , () | Seq 
Completeness {mkℤ (suc n) ff} {T} {0 ! T1' ⇒ T2'} _ | _ , e | _ , e' | Seq{T1}{T2} with ⇒inj{⟦ T1' ⟧}{⟦ T2' ⟧}{L T1}{L T2} e'
Completeness {mkℤ (suc 0) ff} {0 !N} {0 ! T1' ⇒ T2'} _ | _ , () | _ , e' | Seq{T1}{T2} | u1 , u2 
Completeness {mkℤ (suc 0) ff} {suc x !N} {0 ! T1' ⇒ T2'} _ | _ , () | _ , e' | Seq{T1}{T2} | u1 , u2 
Completeness {mkℤ (suc 0) ff} {0 ! A ⇒ B} {0 ! T1' ⇒ T2'} _ | _ , e | _ , e' | Seq{T1}{T2} | u1 , u2 with ⇒inj{⟦ A ⟧}{⟦ B ⟧}{T1}{T2} e
Completeness {mkℤ (suc 0) ff} {0 ! A ⇒ B} {0 ! T1' ⇒ T2'} _ | _ , e | _ , e' | Seq{_}{_} | u1 , u2 | refl , refl
  rewrite L≡++{T1'}{A} u1 | L≡++{T2'}{B} u2 = Clem11
Completeness {mkℤ (suc n) ff} {T} {T'} _ | A , e | B , e' | Pure with ⟦⟧L{T'} e' 
Completeness {mkℤ (suc n) ff} {T} {_} _ | A , e | _ , e' | Pure | A' , refl with ++inv{A'}{L A} e'
Completeness {mkℤ (suc n) ff} {T} {_} _ | A , e | _ , e' | Pure | A' , refl | e1 with ⟦⟧L{A'}{A} e1 
Completeness {mkℤ (suc n) ff} {T} {_} _ | A , e | _ , e' | Pure | A' , refl | e1 | A'' , refl with ++inv{A''}{A} e1 
Completeness {mkℤ (suc n) ff} {T} {_} _ | A , e | _ , e' | Pure | _ , refl | e1 | A'' , refl | u rewrite sym u = <]Tp!++ (Clem12 e)
Completeness {mkℤ (suc n) ff} {T} {T'} _ | A , refl | L B , e' | Cov d with ⟦⟧L{T'}{B} e' 
Completeness {mkℤ 1 ff} {T}  _ | _ , refl | L B , e' | Cov d | M , refl rewrite sym (++inv{M}{B} e') = <]Tp!++{0}{T}{M} (Completeness{0ℤ} d)
Completeness {mkℤ (suc (suc n)) ff} {T}  _ | _ , refl | L B , e' | Cov d | M , refl rewrite sym (++inv{M}{B} e') = <]Tp!++ {suc n} {T} {M} (Completeness{toℤ- (suc n)}{T}{M} d)
Completeness {mkℤ (suc n) ff} {T} {T'} _ | _ , refl | _ , refl | Trans{T2 = T2} d1 d2 with ⟦⟧inv{T2}
Completeness {mkℤ (suc n) ff} {T} {T'} _ | _ , refl | _ , refl | Trans d1 d2 | M , refl =
  trns{T2 = M} (Completeness{toℤ- (suc n)} d1) (Completeness{0ℤ} d2)
