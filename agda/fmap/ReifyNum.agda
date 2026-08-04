module fmap.ReifyNum where
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Empty
open import fmap.Num
import fmap.Decl as D

-- TYPES --

fs : ℕ → D.ty → D.ty
fs (suc n) t = D.f (fs n t)
fs zero t = t

countf : D.ty → ℕ
countf D.base = 0
countf (D.f t) = suc (countf t)
countf (s D.⇒ t) = 0

countf-stable : ∀ {a b} → D.coe a b → countf a ≡ countf b
countf-stable (D.c-id a) = refl
countf-stable (D.c-comp c d) = trans (countf-stable c) (countf-stable d) 
countf-stable (D.c-arr c d) = refl
countf-stable (D.c-mono c) = cong suc (countf-stable c)
countf-stable D.c-fmap = refl

data ty-rep' : D.ty → ty' → Set
data ty-rep : D.ty → ty! → Set
data ty-rep' where
  r-base : ty-rep' D.base base
  _r-⇒_ : {c d : D.ty} {a b : ty!} →
    ty-rep c a →
    ty-rep d b →
    ty-rep' (c D.⇒ d) (a ⇒ b)
data ty-rep where
  r-suc : {n : ℕ} {d : D.ty} {t : ty'} →
    ty-rep d (n ! t) → ty-rep (D.f d) (suc n ! t)
  r-zero : {d : D.ty} {a : ty'} →
    ty-rep' d a →
    ty-rep d (0 ! a)

r-fs : ∀ {d} {t} (n : ℕ) → (pf : ty-rep' d t) → ty-rep (fs n d) (n ! t)
r-fs 0 pf = r-zero pf
r-fs (suc n) pf = r-suc (r-fs n pf)

r-↑ : ∀ {d} {t : ty!} (n : ℕ) → ty-rep d t → ty-rep (fs n d) (n ↑ t)
r-↑ {_} {n ! t} 0 pf = pf
r-↑ {_} {n ! t} (suc m) pf = r-suc (r-↑ m pf)

countf-ty' : ∀ {d t} → ty-rep' d t → countf d ≡ 0
countf-ty' r-base = refl
countf-ty' (ra r-⇒ rb) = refl

countf-ty! : ∀ {d t} → ty-rep d t → countf d ≡ depth t
countf-ty! (r-suc r) = cong suc (countf-ty! r) 
countf-ty! (r-zero r) = countf-ty' r

r-fs-inv : ∀ {d t} → (n : ℕ) → ty-rep (fs n d) (n ! t) → ty-rep' d t
r-fs-inv zero (r-zero r) = r
r-fs-inv (suc n) (r-suc r) = r-fs-inv n r

fs-comm : (n : ℕ) → (a : D.ty) → fs n (D.f a) ≡ D.f (fs n a)
fs-comm 0 a = refl
fs-comm (suc n) a rewrite fs-comm n a = refl

fs-+ : (n m : ℕ) (a : D.ty) →
  fs (n + m) a ≡ fs n (fs m a)
fs-+ zero m a = refl
fs-+ (suc n) m a = cong D.f (fs-+ n m a)

!-inj₁ : ∀ {n m} {a b} →
  n ! a ≡ m ! b →
  n ≡ m
!-inj₁ refl = refl

!-inj₂ : ∀ {n m} {a b} →
  n ! a ≡ m ! b →
  a ≡ b
!-inj₂ refl = refl

r-shift : ∀ {a} {n} {s t} →
  s ≡ suc n ↑ t →
  ty-rep (D.f a) s →
  ty-rep a (n ↑ t)
r-shift {a} {n} {ms ! s} {mt ! t} seq (r-suc r)
  rewrite suc-injective (cong depth seq)
        | cong strip seq = r
r-shift {a} {n} {0 ! s} {mt ! t} seq (r-zero r) =
  ⊥-elim (0≢1+n (cong depth seq))

reify-ty'-r : (t : ty') → Σ[ d ∈ D.ty ] ty-rep' d t
reify-ty-r : (t : ty!) → Σ[ d ∈ D.ty ] ty-rep d t
reify-ty'-r base = D.base , r-base
reify-ty'-r (a ⇒ b) =
  let c , rc = reify-ty-r a in
  let d , rd = reify-ty-r b in
  c D.⇒ d , rc r-⇒  rd
reify-ty-r (n ! t) =
  let d , pf = reify-ty'-r t in
  fs n d , r-fs n pf

eval-ty-r : (a : D.ty) → Σ[ t ∈ ty! ] ty-rep a t
eval-ty'-r : (a : D.ty) → countf a ≡ 0 → Σ[ t ∈ ty' ] ty-rep' a t
eval-ty!-r : (n : ℕ) → (a : D.ty) → Σ[ t ∈ ty! ] ty-rep (fs n a) t
eval-ty-r = eval-ty!-r 0
eval-ty!-r n (D.f a) rewrite (fs-comm n a) =
  eval-ty!-r (suc n) a
eval-ty!-r n D.base = n ! base , r-fs n r-base
eval-ty!-r n (a D.⇒ b) =
  let ta , ra = eval-ty!-r 0 a in
  let tb , rb = eval-ty!-r 0 b in
  n ! ta ⇒ tb , r-fs n (ra r-⇒ rb)

eval-ty'-r D.base pf = base , r-base
eval-ty'-r (a D.⇒ b) pf =
  let ta , ra = eval-ty-r a in
  let tb , rb = eval-ty-r b in
  ta ⇒ tb , (ra r-⇒ rb)

eval-ty : D.ty → ty!
eval-ty t = eval-ty-r t .proj₁

reify-ty : ty! → D.ty
reify-ty t = reify-ty-r t .proj₁

ty-rep'-inj₁ : ∀ {a b} {t} → ty-rep' a t → ty-rep' b t → a ≡ b
ty-rep-inj₁ : ∀ {a b} {t} → ty-rep a t → ty-rep b t → a ≡ b

ty-rep-inj₁ (r-suc ra) (r-suc rb) = cong D.f (ty-rep-inj₁ ra rb)
ty-rep-inj₁ (r-zero ra) (r-zero rb) = ty-rep'-inj₁ ra rb

ty-rep'-inj₁ r-base r-base = refl
ty-rep'-inj₁ (ra r-⇒ rb) (ru r-⇒ rv) =
  cong₂ D._⇒_ (ty-rep-inj₁ ra ru)
              (ty-rep-inj₁ rb rv)

ty-rep'-inj₂ : ∀ {a} {t s} → ty-rep' a t → ty-rep' a s → t ≡ s
ty-rep-inj₂ : ∀ {a} {t s} → ty-rep a t → ty-rep a s → t ≡ s
ty-rep-inj₂ (r-suc rt) (r-suc rs)
  rewrite cong depth (ty-rep-inj₂ rt rs)
        | cong strip (ty-rep-inj₂ rt rs) = refl
ty-rep-inj₂ (r-zero rt) (r-zero rs) rewrite ty-rep'-inj₂ rt rs = refl
ty-rep'-inj₂ r-base r-base = refl
ty-rep'-inj₂ (rs r-⇒ rt) (rw r-⇒ rv)
  rewrite ty-rep-inj₂ rs rw
        | ty-rep-inj₂ rt rv = refl

ty-rep-inj₂n : ∀ {a} {n m} {t s} → ty-rep a (n ! t) → ty-rep a (m ! s) → n ≡ m
ty-rep-inj₂n rn rm = !-inj₁ (ty-rep-inj₂ rn rm)

ty-rep-inj₂t : ∀ {a} {n m} {t s} → ty-rep a (n ! t) → ty-rep a (m ! s) → t ≡ s
ty-rep-inj₂t rn rm = !-inj₂ (ty-rep-inj₂ rn rm)

eval-reify-ty : (t : ty!) → eval-ty (reify-ty t) ≡ t
eval-reify-ty t with reify-ty-r t
...                | a , ra with eval-ty-r a
...                            | b , rb = ty-rep-inj₂ rb ra


reify-eval-ty : (t : D.ty) → reify-ty (eval-ty t) ≡ t
reify-eval-ty t with eval-ty-r t
...                | a , ra with reify-ty-r a
...                            | b , rb = ty-rep-inj₁ rb ra


c-fmaps : {a b : D.ty} → (n : ℕ) → D.coe (a D.⇒ b) (fs n a D.⇒ fs n b)
c-fmaps {a} {b} zero = D.c-id (a D.⇒ b)
c-fmaps {a} {b} (suc n) = D.c-comp (c-fmaps n) D.c-fmap

c-monos : {a b : D.ty} → (n : ℕ) → D.coe a b → D.coe (fs n a) (fs n b)
c-monos zero c = c
c-monos (suc n) c = D.c-mono (c-monos n c)

ty-rep-inv-suc : (t : D.ty) (n : ℕ) (u : ty') →
  ty-rep t (suc n ! u) →
  Σ[ s ∈ D.ty ] t ≡ D.f s × ty-rep s (n ! u)
ty-rep-inv-suc t n u (r-suc pf) = _ , refl , pf

ty-rep-inv-+ : (t : D.ty) (n m : ℕ) (u : ty') →
  ty-rep t ((n + m) ! u) →
  Σ[ s ∈ D.ty ] t ≡ fs n s × ty-rep s (m ! u)
ty-rep-inv-+ t zero m u pf = t , refl , pf
ty-rep-inv-+ t (suc n) m u pf with ty-rep-inv-suc t (n + m) u pf
... | s' , eqn₁ , spf with ty-rep-inv-+ s' n m u spf
...                     | s , eqn₂ , pf' rewrite eqn₁ | eqn₂ = s , refl , pf'

ty-rep-inv-! : (t : D.ty) (n : ℕ) (u : ty') →
  ty-rep t (n ! u) →
  Σ[ s ∈ D.ty ] t ≡ fs n s × ty-rep' s u
ty-rep-inv-! t zero u (r-zero pf) = t , refl , pf
ty-rep-inv-! (D.f t) (suc n) u (r-suc pf)
  with ty-rep-inv-! t n u pf
...  | s , eqs , reps rewrite eqs = s , refl , reps

reify! : ∀ {a b : ty!} {s t : D.ty} → ty-rep s a → ty-rep t b → coe! a b → D.coe s t
reify' : ∀ {a b : ty'} {s t : D.ty} → ty-rep' s a → ty-rep' t b → coe' a b → D.coe s t
reify! (r-suc ra) (r-suc rb) (c-! refl c) = D.c-mono (reify! ra rb (c-! refl c))
reify! (r-zero ra) (r-zero rb) (c-! refl c) = reify' ra rb c
reify' r-base r-base c-base = D.c-id D.base
reify' {(na ! a) ⇒ (nb ! b)}
       {(nu ! u) ⇒ (nv ! v)}
       {a' D.⇒ b'}
       {u' D.⇒ v'}
       (ra r-⇒ rb) (ru r-⇒ rv) (c-⇒ k eqj eqi c d)
  rewrite sym eqi | sym eqj
  with reify-ty'-r a | reify-ty'-r b | reify-ty'-r u | reify-ty'-r v
...  | ao , pfao     | bo , pfbo     | uo , pfuo     | vo , pfvo
     rewrite ty-rep-inj₁ ru (r-fs (k + na) pfuo)
           | ty-rep-inj₁ rv (r-fs (k + nb) pfvo)
           | ty-rep-inj₁ ra (r-fs na pfao)
           | ty-rep-inj₁ rb (r-fs nb pfbo)
           | fs-+ k na uo
           | fs-+ k nb vo =
           let cua = reify' pfuo pfao c in
           let cbv = reify' pfbo pfvo d in
           D.c-comp (D.c-arr (c-monos na cua) (c-monos nb cbv))
                    (c-fmaps k)

c-⇒-wk : {n m i j : ℕ} {a b u v : ty'} →
    {ab uv : ty'} →
    (k : ℕ) →
    k + n ≡ i →
    k + m ≡ j →
    coe' u a →
    coe' b v →
    ab ≡ (n ! a) ⇒ (m ! b) →
    uv ≡ (i ! u) ⇒ (j ! v) →
    coe' ab uv
c-⇒-wk k eqi eqj ua bv eqab equv rewrite eqab | equv = c-⇒ k eqi eqj ua bv

mkid' : (a : ty') → coe' a a
mkid' base = c-base
mkid' ((n ! a) ⇒ (m ! b)) = c-⇒ 0 refl refl (mkid' a) (mkid' b)

mkid! : (a : ty!) → coe! a a
mkid! (n ! a) = c-! refl (mkid' a)

mkcomp! : {a b c : ty!} → coe! a b → coe! b c → coe! a c
mkcomp' : {a b c : ty'} → coe' a b → coe' b c → coe' a c
mkcomp! (c-! eqc c) (c-! eqd d) rewrite eqc | eqd = c-! refl (mkcomp' c d)
mkcomp' c-base c-base = c-base
mkcomp' (c-⇒ k eqc eqd c d) (c-⇒ j equ eqv u v)
  rewrite sym eqv | sym equ =
  c-⇒ (j + k)
      (trans (+-assoc j k _) (cong (_+_ j) eqc))
      (trans (+-assoc j k _) (cong (_+_ j) eqd))
      (mkcomp' u c)
      (mkcomp' d v)

mkarr! : ∀ {a b u v} →
  coe! u a →
  coe! b v →
  coe' (a ⇒ b) (u ⇒ v)
mkarr! {na ! a} {nb ! b} {nu ! u} {nv ! v} (c-! equa c) (c-! eqbv d)
  rewrite equa | eqbv = c-⇒ zero refl refl c d

eval! : ∀ {a b : ty!} {s t : D.ty} → ty-rep s a → ty-rep t b → D.coe s t → coe! a b
eval' : ∀ {a b : ty'} {s t : D.ty} → ty-rep' s a → ty-rep' t b → D.coe s t → coe' a b
eval! ra rb (D.c-id _)
      rewrite ty-rep-inj₂ ra rb = mkid! _
eval! {na ! a} {nb ! b} {s} {t} ra rb (D.c-comp {_} {i} {_} c d) =
  let t' , ri = eval-ty-r i in
  mkcomp! (eval! ra ri c) (eval! ri rb d)
eval! {0 ! ((na ! a) ⇒ (nb ! b))} {0 ! ((nu ! u) ⇒ (nv ! v))} {a' D.⇒ b'} {u' D.⇒ v'} (r-zero (ra r-⇒ rb)) (r-zero (ru r-⇒ rv)) (D.c-arr c d)
    = c-! refl (eval' (ra r-⇒ rb) (ru r-⇒ rv) (D.c-arr c d))
eval! {na ! a} {nb ! b} {s} {t} (r-suc ra) (r-suc rb) (D.c-mono c)
  with eval! ra rb c
...  | c-! pf c' = c-! (cong suc pf) c'
eval! {0 ! (na₁ ! a₁) ⇒ (na₂ ! a₂)} {0 ! b} {u D.⇒ v} {D.f u D.⇒ D.f v}
      (r-zero (ru r-⇒ rv)) (r-zero (r-suc ru' r-⇒ r-suc rv')) D.c-fmap
      rewrite ty-rep-inj₂n ru' ru
            | ty-rep-inj₂t ru' ru
            | ty-rep-inj₂n rv' rv
            | ty-rep-inj₂t rv' rv =
      c-! refl (c-⇒ 1 refl refl (mkid' _) (mkid' _))
eval' ra rb (D.c-id a) rewrite ty-rep'-inj₂ ra rb = mkid' _
eval' ra rb (D.c-comp {a} {e} {b} c d) =
  let te , re = eval-ty'-r e (trans (sym (countf-stable c)) (countf-ty' ra)) in
  mkcomp' (eval' ra re c) (eval' re rb d)
eval' {(na' ! a') ⇒ (nb' ! b')} {(nu' ! u') ⇒ (nv' ! v')} {a D.⇒ b} {u D.⇒ v}
  (ra r-⇒ rb)
  (ru r-⇒ rv)
  (D.c-arr c d)
  with ty-rep-inv-! _ _ _ ra
     | ty-rep-inv-! _ _ _ rb
     | ty-rep-inv-! _ _ _ ru
     | ty-rep-inv-! _ _ _ rv
...  | a0 , aeq , arep
     | b0 , beq , brep
     | u0 , ueq , urep
     | v0 , veq , vrep
     rewrite aeq | beq | ueq | veq
  = mkarr! (eval! ru ra c) (eval! rb rv d)
eval' {u} {v} {a D.⇒ b} {D.f a D.⇒ D.f b}
  (_r-⇒_ {a} {b} {a'} {b'} ra rb)
  (_r-⇒_ {D.f a} {D.f b} {fa'} {fb'} (r-suc rfa) (r-suc rfb)) D.c-fmap
  rewrite sym (ty-rep-inj₂ rfa ra)
        | sym (ty-rep-inj₂ rfb rb)
  = c-⇒ 1 refl refl (mkid' _) (mkid' _)
