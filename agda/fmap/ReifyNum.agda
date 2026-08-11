module fmap.ReifyNum where
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
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

reify-ty'-r : (t : ty') → Σ[ d ∈ D.ty ] ty-rep' d t
reify-ty-r : (t : ty!) → Σ[ d ∈ D.ty ] ty-rep d t
reify-ty'-r base = D.base , r-base
reify-ty'-r (a ⇒ b) =
  let c , rc = reify-ty-r a in
  let d , rd = reify-ty-r b in
  c D.⇒ d , rc r-⇒  rd
reify-ty-r (zero ! t) =
  let d , pf = reify-ty'-r t in
  d , r-zero pf
reify-ty-r (suc n ! t) =
  let d , pf = reify-ty-r (n ! t) in
  D.f d , r-suc pf


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

r-fs-eq : ∀ {fa n a a'}
  (r! : ty-rep fa (n ! a')) →
  (r : ty-rep' a a') →
  fa ≡ fs n a
r-fs-eq {_} {n} r! r = ty-rep-inj₁ r! (r-fs n r)

ty-rep-uniq : ∀ {a a'} →
  (r₁ r₂ : ty-rep a a') →
  r₁ ≡ r₂
ty-rep'-uniq : ∀ {a a'} →
  (r₁ r₂ : ty-rep' a a') →
  r₁ ≡ r₂
ty-rep-uniq (r-zero r) (r-zero r') = cong r-zero (ty-rep'-uniq r r')
ty-rep-uniq (r-suc r) (r-suc r') = cong r-suc (ty-rep-uniq r r')
ty-rep'-uniq {D.base} {base} r-base r-base = refl
ty-rep'-uniq {a D.⇒ b} {a' ⇒ b'} (ra r-⇒ rb) (ra' r-⇒ rb')
  = cong₂ _r-⇒_ (ty-rep-uniq ra ra') (ty-rep-uniq rb rb')

r-fs-eq-r : ∀ {n a a'}
  (r! : ty-rep (fs n a) (n ! a')) →
  (r : ty-rep' a a') →
  r! ≡ r-fs n r
r-fs-eq-r r! r = ty-rep-uniq _ _

c-fmaps : {a b : D.ty} → (n : ℕ) → D.coe (a D.⇒ b) (fs n a D.⇒ fs n b)
c-fmaps {a} {b} zero = D.c-id (a D.⇒ b)
c-fmaps {a} {b} (suc n) = D.c-comp (c-fmaps n) D.c-fmap

c-monos : {a b : D.ty} → (n : ℕ) → D.coe a b → D.coe (fs n a) (fs n b)
c-monos zero c = c
c-monos (suc n) c = D.c-mono (c-monos n c)

c-monos-proper :
  {a b : D.ty} → (n : ℕ) → (c d : D.coe a b) →
  c D.≃ d →
  c-monos n c D.≃ c-monos n d
c-monos-proper {a} zero c d pf = pf
c-monos-proper {a} (suc n) c d pf = D.c-cong-mono (c-monos-proper n c d pf)

c-monos-id :
  {a : D.ty} → (n : ℕ) → (c : D.coe a a) →
  c D.≃ D.c-id a →
  c-monos n c D.≃ D.c-id (fs n a)
c-monos-id zero c pf = pf
c-monos-id (suc n) c pf = D.c-trans (D.c-cong-mono (c-monos-id n c pf)) D.c-mono-id

c-monos-rep : {a b u v : D.ty} {a' b' : ty'} →
  (n : ℕ) →
  ty-rep' a a' →
  ty-rep' b b' →
  ty-rep u (n ! a') →
  ty-rep v (n ! b') →
  D.coe a b →
  D.coe u v
c-monos-rep zero ra rb (r-zero ru) (r-zero rv) c =
  subst₂ D.coe (ty-rep'-inj₁ ra ru) (ty-rep'-inj₁ rb rv) c
c-monos-rep (suc n) ra rb (r-suc ru) (r-suc rv) c =
  D.c-mono (c-monos-rep n ra rb ru rv c)

c-monos-rep-id :
  {a u : D.ty} {a' : ty'} →
  (n : ℕ) →
  (ra rb : ty-rep' a a') →
  (ru rv : ty-rep u (n ! a')) →
  (c : D.coe a a) →
  c D.≃ D.c-id a →
  c-monos-rep n ra ra ru ru c D.≃ D.c-id u
c-monos-rep-id zero ra rb (r-zero ru) (r-zero rv) c pf
  with ty-rep'-inj₁ ra ru | ty-rep'-inj₁ ra ru
...  | refl | refl = pf
c-monos-rep-id (suc n) ra rb (r-suc ru) (r-suc rv) c pf =
  D.c-trans (D.c-cong-mono (c-monos-rep-id n ra ra ru rv c pf)) D.c-mono-id

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
  (r : ty-rep t (n ! u)) →
  Σ[ s ∈ D.ty ] t ≡ fs n s × ty-rep' s u
ty-rep-inv-! t zero u (r-zero pf) = t , refl , pf
ty-rep-inv-! (D.f t) (suc n) u (r-suc pf)
  with ty-rep-inv-! t n u pf
...  | s , eqs , reps rewrite eqs = s , refl , reps

mkfmap : ∀ na nb a b → coe' ((na ! a) ⇒ (nb ! b)) ((suc na ! a) ⇒ (suc nb ! b))
mkfmap na nb a b = {!!}

reify! : ∀ {a b : ty!} {s t : D.ty} → ty-rep s a → ty-rep t b → coe! a b → D.coe s t
reify' : ∀ {a b : ty'} {s t : D.ty} → ty-rep' s a → ty-rep' t b → coe' a b → D.coe s t
reify! {n ! a} {n ! b} {s} {t} ra rb (c-! refl c)
  with ty-rep-inv-! _ _ _ ra | ty-rep-inv-! _ _ _ rb
...  | a' , refl , ra'       | b' , refl , rb'
  with r-fs-eq-r ra ra' | r-fs-eq-r rb rb'
...  | refl             | refl
  = c-monos n (reify' ra' rb' c)
reify' r-base r-base c-base = D.c-id D.base
reify' {a ⇒ b}
       {uu ⇒ vv}
       {a' D.⇒ b'}
       {u' D.⇒ v'}
       (ra r-⇒ rb) (ru r-⇒ rv) (c-⇒ {a} {b} {nu ! u} {nv ! v} zero refl refl c d)
       = D.c-arr (reify! ru ra c) (reify! rb rv d)
reify' {a ⇒ b}
       {uu ⇒ vv}
       {a' D.⇒ b'}
       {D.f u' D.⇒ D.f v'}
       (ra r-⇒ rb) (r-suc ru r-⇒ r-suc rv) (c-⇒ {a} {b} {nu ! u} {nv ! v} (suc k) refl refl c d)
      = D.c-comp (reify' (ra r-⇒ rb) (ru r-⇒ rv) (c-⇒ k refl refl c d)) D.c-fmap

data _≈_ : ∀ {a b u v} → D.coe a b → D.coe u v → Set where
  heq : ∀ a b c d → c D.≃ d → c ≈ d

mkid' : (a : ty') → coe' a a
mkid! : (a : ty!) → coe! a a

↑-zero : ∀ a → zero ↑ a ≡ a
↑-zero (n ! a) = refl

mkid' base = c-base
mkid' (a ⇒ b) = c-⇒ 0 (sym (↑-zero a)) (sym (↑-zero b)) (mkid! a) (mkid! b)
mkid! (n ! a) = c-! refl (mkid' a)

fmap-l : ∀ {na a nb b u} → coe' ((suc na ! a) ⇒ (suc nb ! b)) u → coe' ((na ! a) ⇒ (nb ! b)) u
fmap-l (c-⇒ k refl refl (c-! refl c) (c-! refl d))
    = c-⇒ (suc k)
          (cong₂ _!_ (+-suc _ _) refl)
          (cong₂ _!_ (+-suc _ _) refl)
          (c-! refl c)
          (c-! refl d)

mkcomp! : {a b c : ty!} → coe! a b → coe! b c → coe! a c
mkcomp' : {a b c : ty'} → coe' a b → coe' b c → coe' a c
mkcomp-arr-l : ∀ {a b u v f} → (k : ℕ) → (j : ℕ) →
  coe! u a →
  coe! b v →
  coe' ((k ↑ u) ⇒ (k ↑ v)) f →
  coe' (a ⇒ b) f
mkcomp-arr-l {a} {b} {nu ! u} {nv ! v} {uu ⇒ vv}
  zero c d
  (c-⇒ {a'} {b'} {u'} {v'} j refl refl cc dd)
  = c-⇒ j refl refl (mkcomp! cc c) (mkcomp! d dd)
mkcomp-arr-l {a} {b} {nu ! u} {nv ! v} (suc k) c d (c-⇒ j refl refl (c-! refl cc) (c-! refl dd))
  = mkcomp-arr-l k c d
      (c-⇒ (suc j)
          (cong₂ _!_ (+-suc _ _) refl)
          (cong₂ _!_ (+-suc _ _) refl)
          (c-! refl cc)
          (c-! refl dd))
mkcomp! (c-! refl c) (c-! refl d) = c-! refl (mkcomp' c d)
mkcomp' c-base c-base = c-base
mkcomp' (c-⇒ k refl refl c d) cc = mkcomp-arr-l k c d cc

{-
mkarr! : ∀ {a b u v} →
  coe! u a →
  coe! b v →
  coe' (a ⇒ b) (u ⇒ v)
mkarr! {na ! a} {nb ! b} {nu ! u} {nv ! v} (c-! refl c) (c-! refl d) =
  c-⇒ zero c d

eval! : ∀ {a b : ty!} {s t : D.ty} → ty-rep s a → ty-rep t b → D.coe s t → coe! a b
eval' : ∀ {a b : ty'} {s t : D.ty} → ty-rep' s a → ty-rep' t b → D.coe s t → coe' a b
eval! ra rb (D.c-id _)
      rewrite ty-rep-inj₂ ra rb = mkid! _
eval! {na ! a} {nb ! b} {s} {t} ra rb (D.c-comp {_} {i} {_} c d) =
  let t' , ri = eval-ty-r i in
  mkcomp! (eval! ra ri c) (eval! ri rb d)
eval! (r-zero r) (r-zero r') (D.c-arr c d) = c-! refl (eval' r r' (D.c-arr c d))
eval! {suc na ! a} {suc nb ! b} {s} {t} (r-suc ra) (r-suc rb) (D.c-mono c)
  with eval! ra rb c
...  | c-! pf c' = c-! (cong suc pf) c'
eval! (r-zero r) (r-zero r') D.c-fmap =
  c-! refl (eval' r r' D.c-fmap)
eval' ra rb (D.c-id a) rewrite ty-rep'-inj₂ ra rb = mkid' _
eval' ra rb (D.c-comp {a} {e} {b} c d) =
  let te , re = eval-ty'-r e (trans (sym (countf-stable c)) (countf-ty' ra)) in
  mkcomp' (eval' ra re c) (eval' re rb d)
eval' (ra r-⇒ rb)
      (ru r-⇒ rv)
      (D.c-arr c d) = mkarr! (eval! ru ra c) (eval! rb rv d)
eval' {u} {v} {a D.⇒ b} {D.f a D.⇒ D.f b}
  (_r-⇒_ {a} {b} {a'} {b'} ra rb)
  (_r-⇒_ {D.f a} {D.f b} {na' ! fa'} {nb' ! fb'} (r-suc rfa) (r-suc rfb)) D.c-fmap
  with ty-rep-inj₂ rfa ra | ty-rep-inj₂ rfb rb
...  | refl               | refl =
  c-⇒ 1 (mkid' fa') (mkid' fb')

c-monos-comp : {a b c : D.ty} {c1 : D.coe a b} {c2 : D.coe b c} →
  (n : ℕ) →
  c-monos n (c1 D.· c2) D.≃ c-monos n c1 D.· c-monos n c2
c-monos-comp zero = D.c-refl (c-monos zero (_ D.· _))
c-monos-comp (suc n) = D.c-trans (D.c-cong-mono (c-monos-comp n)) D.c-mono-comp


reify-mkcomp! :
  ∀ {a e b s e' t} →
  (ra : ty-rep s a) →
  (rb : ty-rep t b) →
  (re : ty-rep e' e) →
  (c : coe! a e) →
  (d : coe! e b) →
  reify! ra rb (mkcomp! c d) D.≃ D.c-comp (reify! ra re c) (reify! re rb d)
reify-mkcomp' :
  ∀ {a e b s e' t} →
  (ra : ty-rep' s a) →
  (rb : ty-rep' t b) →
  (re : ty-rep' e' e) →
  (c : coe' a e) →
  (d : coe' e b) →
  reify' ra rb (mkcomp' c d) D.≃ D.c-comp (reify' ra re c) (reify' re rb d)
reify-mkcomp! {na ! a} {ne ! e} {nb ! b} {s} {e'} {t} ra rb re (c-! refl c) (c-! refl d)
  with ty-rep-inv-! s na a ra | ty-rep-inv-! t na b rb | ty-rep-inv-! e' na e re
...  | a' , refl , ra' | b' , refl , rb' | eo , refl , reo
  with ty-rep-uniq ra (r-fs na ra') | ty-rep-uniq rb (r-fs na rb')
     | ty-rep-uniq re (r-fs na reo) | ty-rep-uniq re (r-fs na reo)
... | refl | refl | refl | refl
    = D.c-trans
        (c-monos-proper na _ _ (reify-mkcomp' ra' rb' reo c d))
        (c-monos-comp na)
reify-mkcomp' {a} {e} {b} {s} {e'} {t} r-base r-base r-base c-base c-base
  = {!!}
reify-mkcomp'
  {(na ! a) ⇒ (nb ! b)} {(ne ! e) ⇒ (nf ! f)} {(_ ! u) ⇒ (_ ! v)}
  {a' D.⇒ b'} {e' D.⇒ f'} {u' D.⇒ v'}
  (ra r-⇒ rb)
  (re r-⇒ rf) (ru r-⇒ rv)
  (c-⇒ k c d) (c-⇒ k' c' d')
  = {!!}

reify-mkid! :
  ∀ {a s} →
  (ra rb : ty-rep s a) →
  reify! ra rb (mkid! a) D.≃ D.c-id s
reify-mkid' :
  ∀ {a s} →
  (ra rb : ty-rep' s a) →
  reify' ra rb (mkid' a) D.≃ D.c-id s
reify-mkid! {n ! a} {s} ra rb
  with ty-rep-uniq ra rb
...  | refl
  with ty-rep-inv-! s n a ra
...  | a' , refl , ra'
  with ty-rep-uniq ra (r-fs n ra') | ty-rep-uniq ra (r-fs n ra')
... | refl | refl
  = c-monos-id n _ (reify-mkid' ra' ra')
reify-mkid' {base} {D.base} r-base r-base = {!!}
reify-mkid' {(na ! a) ⇒ (nb ! b)} {s D.⇒ t} (ra r-⇒ rb) (ru r-⇒ rv) = {!!}

reify-eval! : ∀ {a b s t} → (ra : ty-rep s a) → (rb : ty-rep t b) → (c : D.coe s t) → reify! ra rb (eval! ra rb c) D.≃ c
reify-eval' : ∀ {a b s t} → (ra : ty-rep' s a) → (rb : ty-rep' t b) → (c : D.coe s t) → reify' ra rb (eval' ra rb c) D.≃ c
reify-eval! ra rb (D.c-id a) with ty-rep-inj₂ ra rb
... | refl = reify-mkid! ra rb
reify-eval! {na ! a} {nb ! b} {s} {t} ra rb (D.c-comp {_} {i} {_} c d) =
  let e , re = eval-ty-r i in
  let pf = reify-mkcomp! ra rb re (eval! ra re c) (eval! re rb d) in
  D.c-trans pf
            (D.c-cong-comp (reify-eval! ra re c) (reify-eval! re rb d))
reify-eval! {zero ! (na ! a) ⇒ (nb ! b)} {zero ! (nu ! u) ⇒ (nv ! v)}
  {a' D.⇒ b'} {u' D.⇒ v'}
  (r-zero (ra r-⇒ rb)) (r-zero (ru r-⇒ rv))
  (D.c-arr c d)
  = {!!}
reify-eval! {suc n ! a} {suc n' ! b} {D.f s} {D.f t} (r-suc ra) (r-suc rb) (D.c-mono c)
  with eval! ra rb c | reify-eval! ra rb c
...  | c-! refl c'   | pf
  with ty-rep-inv-! (D.f s) (suc n) a (r-suc ra) | ty-rep-inv-! s n a ra
     | ty-rep-inv-! (D.f t) (suc n) b (r-suc rb) | ty-rep-inv-! t n b rb
... | sa' , refl , rsa' | a' , eqa' , ra'
    | sb' , refl , rsb' | b' , eqb' , rb'
  with ty-rep'-inj₁ rsa' ra' | ty-rep'-inj₁ rsb' rb' | eqa' | eqb'
... | refl | refl | refl | refl
  with ty-rep-uniq ra (r-fs n ra') | ty-rep-uniq rb (r-fs n rb')
...  | refl | refl
  with cong r-suc (ty-rep-uniq ra (r-fs n ra'))
     | cong r-suc (ty-rep-uniq rb (r-fs n rb'))
... | refl | refl
  = D.c-cong-mono pf
reify-eval! {zero ! u} {zero ! v} {a D.⇒ b} {D.f a D.⇒ D.f b}
  (r-zero (_r-⇒_ {a} {b} {na ! a'} {nb ! b'} ra rb))
  (r-zero (_r-⇒_ {D.f a} {D.f b} {na' ! fa'} {nb' ! fb'} (r-suc rfa) (r-suc rfb))) D.c-fmap
  = {!!}

reify-eval' ra rb (D.c-id a) with ty-rep'-inj₂ ra rb
... | refl = reify-mkid' ra rb
reify-eval' ra rb (D.c-comp {a} {e} {b} c d) =
  let te , re = eval-ty'-r e (trans (sym (countf-stable c)) (countf-ty' ra)) in
  let pf = reify-mkcomp' ra rb re (eval' ra re c) (eval' re rb d) in
  D.c-trans pf (D.c-cong-comp (reify-eval' ra re c) (reify-eval' re rb d))
reify-eval' {(na ! a) ⇒ (nb ! b)}
       {(nu ! u) ⇒ (nv ! v)}
       {a' D.⇒ b'}
       {u' D.⇒ v'}
       (ra r-⇒ rb) (ru r-⇒ rv) (D.c-arr c d) = {!!}
reify-eval' {u} {v} {a D.⇒ b} {D.f a D.⇒ D.f b}
  (_r-⇒_ {a} {b} {na ! a'} {nb ! b'} ra rb)
  (_r-⇒_ {D.f a} {D.f b} {na' ! fa'} {nb' ! fb'} (r-suc rfa) (r-suc rfb)) D.c-fmap = {!!}
-}
