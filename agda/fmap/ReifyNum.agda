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
  r-! : ∀ {d t} → (n : ℕ) →
    ty-rep' d t →
    ty-rep (fs n d) (n ! t)


r-fs : ∀ {d} {t} (n : ℕ) → (pf : ty-rep' d t) → ty-rep (fs n d) (n ! t)
r-fs n pf = r-! n pf

countf-ty' : ∀ {d t} → ty-rep' d t → countf d ≡ 0
countf-ty' r-base = refl
countf-ty' (ra r-⇒ rb) = refl

countf-ty! : ∀ {d t} → ty-rep d t → countf d ≡ depth t
countf-ty! r = {!!}

r-fs-inv : ∀ {d t} → (n : ℕ) → ty-rep (fs n d) (n ! t) → ty-rep' d t
r-fs-inv n r = {!!}

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
  d , r-! 0 pf
reify-ty-r (suc n ! t) =
  let d , pf = reify-ty-r (n ! t) in
  D.f d , {!!}


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
  n ! (ta ⇒ tb) , r-fs n (ra r-⇒ rb)

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

ty-rep-inj₁ ra rb = {!!}

ty-rep'-inj₁ r-base r-base = refl
ty-rep'-inj₁ (ra r-⇒ rb) (ru r-⇒ rv) =
  cong₂ D._⇒_ (ty-rep-inj₁ ra ru)
              (ty-rep-inj₁ rb rv)

ty-rep'-inj₂ : ∀ {a} {t s} → ty-rep' a t → ty-rep' a s → t ≡ s
ty-rep-inj₂ : ∀ {a} {t s} → ty-rep a t → ty-rep a s → t ≡ s
ty-rep-inj₂ rt rs = {!!}
ty-rep'-inj₂ rt rs = {!!}

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
ty-rep-uniq r r' = {!!}
ty-rep'-uniq r r' = {!!}

r-fs-eq-r : ∀ {n a a'}
  (r! : ty-rep (fs n a) (n ! a')) →
  (r : ty-rep' a a') →
  r! ≡ r-fs n r
r-fs-eq-r r! r = ty-rep-uniq _ _

c-fmaps : {a b : D.ty} →
  (n : ℕ) →
  D.coe (a D.⇒ b) (fs n a D.⇒ fs n b)
c-fmaps {a} {b} zero = D.c-id (a D.⇒ b)
c-fmaps {a} {b} (suc n) = D.c-comp (c-fmaps n ) D.c-fmap

c-monos : {a b : D.ty} → (n : ℕ) → D.coe a b → D.coe (fs n a) (fs n b)
c-monos zero c = c
c-monos (suc n) c = D.c-mono (c-monos n c)

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
c-monos-rep n ra rb ru rv c = {!!}

{-
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
  -}

ty-rep-inv-suc : (t : D.ty) (n : ℕ) (u : ty') →
  ty-rep t (suc n ! u) →
  Σ[ s ∈ D.ty ] t ≡ D.f s × ty-rep s (n ! u)
ty-rep-inv-suc t n u r = {!!}

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
ty-rep-inv-! t n u r = {!!}

reify! : ∀ {a b : ty!} {s t : D.ty} → ty-rep s a → ty-rep t b → coe! a b → D.coe s t
reify' : ∀ {a b : ty'} {s t : D.ty} → ty-rep' s a → ty-rep' t b → coe' a b → D.coe s t
reify! {n ! a} {n ! b} {s} {t} (r-! na ra) (r-! nb rb) (c-! refl c)
  = c-monos n (reify' ra rb c)
reify' r-base r-base c-base = D.c-id D.base
reify'
  {_ ! _ ⇒ _ ! _}
  {_ ! _ ⇒ _ ! _}
  ((r-! na ra) r-⇒ (r-! nb rb))
  ((r-! nu ru) r-⇒ (r-! nv rv))
  (c-⇒ zero (c-! refl c) (c-! refl d))
  =
  let c' = reify' ru ra c in
  let d' = reify' rb rv d in
  D.c-arr (c-monos na c') (c-monos nb d')
reify'
  (r-! na ra r-⇒ r-! nb rb)
  (r-! nu ru r-⇒ r-! nv rv)
  (c-⇒ (suc k) (c-! refl c) (c-! refl d))
  =
  D.c-comp (reify' (r-! na ra r-⇒ r-! _ rb)
                   (r-! _ ru r-⇒ r-! _ rv)
                   (c-⇒ k (c-! refl c) (c-! refl d)))
           D.c-fmap

infix 4 _≈_
data _≈_ : ∀ {a b u v} → D.coe a b → D.coe u v → Set where
  heq : ∀ {a b} {c d : D.coe a b} → c D.≃ d → c ≈ d
  heq_MAGIC : ∀ {a b u v} {c : D.coe a b} {d : D.coe u v} → c ≈ d

mkid' : (a : ty') → coe' a a
mkid! : (a : ty!) → coe! a a

↑-zero : ∀ a → zero ↑ a ≡ a
↑-zero (n ! a) = refl

mkid' base = c-base
mkid' (a ⇒ b) = {!!}
mkid! (n ! a) = c-! refl (mkid' a)

fmap-l : ∀ {na a nb b u} → coe' ((suc na ! a) ⇒ (suc nb ! b)) u → coe' ((na ! a) ⇒ (nb ! b)) u
fmap-l cc = {!!}

{-
fmaps-l : ∀ {a b u} → (k : ℕ) → coe' ((k ↑ a) ⇒ (k ↑ b)) u → coe' (a ⇒ b) u
fmaps-l {na ! a} {nb ! b} k (c-⇒ j refl refl (c-! refl c) (c-! refl d))
    = c-⇒ (j + k)
          (cong₂ _!_ (sym (+-assoc j k na)) refl)
          (cong₂ _!_ (sym (+-assoc j k nb)) refl)
          (c-! refl c)
          (c-! refl d)
-}

c-⇒-wk : {na nb : ℕ} {a b : ty'} {nu nv : ℕ} {u v : ty'} {f : ty'} →
  (k : ℕ) →
  f ≡ ((k + nu) ! u ⇒ (k + nv) ! v) →
  coe! (nu ! u) (na ! a) →
  coe! (nb ! b) (nv ! v) →
  coe' (na ! a ⇒ nb ! b) f
c-⇒-wk k refl c d = c-⇒ k c d

coe-cast₁ : ∀ {a b u} {c : D.coe a b} →
  (bv : a ≡ u) →
  c ≈ subst (λ x → D.coe x b) bv c
coe-cast₁ refl = heq (D.c-refl _)

coe-cast₂ : ∀ {a b v} {c : D.coe a b} →
  (bv : b ≡ v) →
  c ≈ subst (λ x → D.coe a x) bv c
coe-cast₂ refl = heq (D.c-refl _)

≈-refl : ∀ {a b} (c : D.coe a b) → c ≈ c
≈-refl c = heq (D.c-refl c)

≈-sym : ∀ {a b} {u v} {c : D.coe a b} {d : D.coe u v} →
  c ≈ d →
  d ≈ c
≈-sym (heq pf) = heq (D.c-sym pf)
≈-sym heq_MAGIC = heq_MAGIC

≈-trans : ∀ {a₁ b₁ a₂ b₂ a₃ b₃ : D.ty} →
  {c₁ : D.coe a₁ b₁} →
  {c₂ : D.coe a₂ b₂} →
  {c₃ : D.coe a₃ b₃} →
  c₁ ≈ c₂ →
  c₂ ≈ c₃ →
  c₁ ≈ c₃
≈-trans (heq pf1) (heq pf2) = heq (D.c-trans pf1 pf2)
≈-trans _ _ = heq_MAGIC

c-monos-proper :
  {a b : D.ty} → {c : D.coe a b} →
  {u v : D.ty} → {d : D.coe u v} →
  (n : ℕ) →
  a ≡ u →
  b ≡ v →
  c ≈ d →
  c-monos n c ≈ c-monos n d
c-monos-proper {a} zero pf = {!!}
c-monos-proper {a} (suc n) pf = {!!}


mkfmap :
  ∀ {na nb nu nv}
    {a b u v} →
  coe' (na ! a ⇒ nb ! b) (nu ! u ⇒ nv ! v) →
  coe' (na ! a ⇒ nb ! b) (suc nu ! u ⇒ suc nv ! v)
mkfmap (c-⇒ k c d) = c-⇒ (suc k) c d

mkfmaps :
  ∀ {na nb nu nv}
    {a b u v} →
    (k : ℕ) →
    coe' (na ! a ⇒ nb ! b) (nu ! u ⇒ nv ! v) →
    coe' (na ! a ⇒ nb ! b) ((k + nu) ! u ⇒ (k + nv) ! v)
mkfmaps zero c = c
mkfmaps (suc k) c = mkfmap (mkfmaps k c)

reify-mkfmap :
  ∀ {na nb nu nv}
    {a b u v} →
    {a' b' u' v' : D.ty} →
    (ra : ty-rep' (a' D.⇒ b') (na ! a ⇒ nb ! b)) →
    (rb : ty-rep' (u' D.⇒ v') (nu ! u ⇒ nv ! v)) →
    (rb' : ty-rep' (D.f u' D.⇒ D.f v') (suc nu ! u ⇒ suc nv ! v)) →
    (c : coe' (na ! a ⇒ nb ! b) (nu ! u ⇒ nv ! v)) →
  reify' ra rb' (mkfmap c) D.≃ D.c-comp (reify' ra rb c) D.c-fmap
reify-mkfmap ra rb rb' c = {!!}

mkcomp! : {a b c : ty!} → coe! a b → coe! b c → coe! a c
mkcomp' : {a b c : ty'} → coe' a b → coe' b c → coe' a c
mkcomp-arr :
  {na nb ne nf nu nv : ℕ} →
  {a b e f u v : ty'} →
  (k j : ℕ) →
  (eqau : na ≡ nu) →
  (eqvb : nv ≡ nb) →
  (c : coe' e a) →
  (c' : coe' b f) →
  (d : coe' u e) →
  (d' : coe' f v) →
  coe' (na ! a ⇒ nb ! b) ((j + (k + nu)) ! u ⇒ (j + (k + nv)) ! v)
mkcomp-arr k zero eqau eqvb c c' d d' =
  c-⇒ k (c-! eqau (mkcomp' d c)) (c-! eqvb (mkcomp' c' d'))
mkcomp-arr k (suc j) eqau eqvb c c' d d' =
  mkfmap (mkcomp-arr k j eqau eqvb c c' d d')
mkcomp! (c-! refl c) (c-! refl d) = c-! refl (mkcomp' c d)
mkcomp' c-base c-base = c-base
mkcomp' (c-⇒ k (c-! refl c) (c-! refl d)) (c-⇒ j (c-! refl cc) (c-! refl dd)) =
  mkcomp-arr k j refl refl c d cc dd

mkarr! : ∀ {a b u v} →
  coe! u a →
  coe! b v →
  coe' (a ⇒ b) (u ⇒ v)
mkarr! {na ! a} {nb ! b} {nu ! u} {nv ! v} c d =
  c-⇒ zero c d

h-cong-mono :
  {a b u v : D.ty} →
  {c : D.coe a b} →
  {d : D.coe u v} →
  c ≈ d →
  D.c-mono c ≈ D.c-mono d
h-cong-mono (heq pf) = heq (D.c-cong-mono pf)
h-cong-mono _ = heq_MAGIC

h-cong-arr :
  {a₁ b₁ u₁ v₁ : D.ty} →
  {a₂ b₂ u₂ v₂ : D.ty} →
  {c₁ : D.coe a₁ b₁} →
  {d₁ : D.coe u₁ v₁} →
  {c₂ : D.coe a₂ b₂} →
  {d₂ : D.coe u₂ v₂} →
  c₁ ≈ c₂ →
  d₁ ≈ d₂ →
  D.c-arr c₁ d₁ ≈ D.c-arr c₂ d₂
h-cong-arr eq1 eq2 = {!!}

h-cong-comp :
  {a b c u v w : D.ty} →
  {c₁ : D.coe a b} →
  {c₂ : D.coe b c} →
  {d₁ : D.coe u v} →
  {d₂ : D.coe v w} →
  c₁ ≈ d₁ →
  c₂ ≈ d₂ →
  D.c-comp c₁ c₂ ≈ D.c-comp d₁ d₂
h-cong-comp p q = {!!}

h-fmap-refl : ∀ {a b u v} →
  a ≡ u →
  b ≡ v →
  D.c-fmap {a} {b} ≈ D.c-fmap {u} {v}
h-fmap-refl refl refl = heq (D.c-refl _)

h-fmaps-refl : ∀ {a b u v} → (k : ℕ) →
  a ≡ u →
  b ≡ v →
  c-fmaps {a} {b} k ≈ c-fmaps {u} {v} k
h-fmaps-refl k eqa eqb = {!!}

reify-arr :
  {a' b' u' v' : D.ty} →
  {a b u v : ty'} →
  {ra : ty-rep' a' a} →
  {rb : ty-rep' b' b} →
  {ru : ty-rep' u' u} →
  {rv : ty-rep' v' v} →
  (k na nb : ℕ) →
  (c : coe' u a) →
  (d : coe' b v) →
  reify'
    (r-! na ra r-⇒ r-! nb rb)
    (r-! (k + na) ru r-⇒ r-! (k + nb) rv)
    (c-⇒ k (c-! refl c) (c-! refl d)) ≈
      (D.c-comp (D.c-arr (c-monos na (reify' ru ra c)) (c-monos nb (reify' rb rv d)))
                (c-fmaps k))
reify-arr zero na nb c d = heq (D.c-sym D.c-id-r)
reify-arr (suc k) na nb c d =
  let pf = reify-arr k na nb c d in
  ≈-trans (h-cong-comp pf (h-fmap-refl (fs-+ k na _) (fs-+ k nb _)))
          (heq D.c-comp-assoc)

c-monos-+ : ∀ {j k c} →
  c-monos (j + k) c ≈ c-monos j (c-monos k c)
c-monos-+ {zero} {k} {c} = heq (D.c-refl (c-monos (zero + k) c))
c-monos-+ {suc j} {k} {c} = h-cong-mono c-monos-+

c-monos-comp : ∀ {u v w} {c : D.coe u v} {d : D.coe v w} (k : ℕ) →
  c-monos k (D.c-comp c d) ≈ D.c-comp (c-monos k c) (c-monos k d)
c-monos-comp k = {!!}

c-fmaps-+ : {a b : D.ty} (m n : ℕ) →
  c-fmaps {a} {b} (m + n) ≈ D.c-comp (c-fmaps {a} {b} n) (c-fmaps {fs n a} {fs n b} m)
c-fmaps-+ {a} {b} zero n = heq (D.c-sym D.c-id-r)
c-fmaps-+ {a} {b} (suc m) n =
  ≈-trans (h-cong-comp
            (c-fmaps-+ {a} {b} m n)
            (h-fmap-refl (fs-+ m n _) (fs-+ m n _)))
          (heq D.c-comp-assoc)

c-arrs-fmap : {a b u v : D.ty} {c1 : D.coe a b} {c2 : D.coe u v} (k : ℕ) →
  D.c-comp (c-fmaps k) (D.c-arr (c-monos k c1) (c-monos k c2)) D.≃ D.c-comp (D.c-arr c1 c2) (c-fmaps k)
c-arrs-fmap zero = D.c-trans D.c-id-l (D.c-sym D.c-id-r)
c-arrs-fmap (suc k) =
  D.c-trans
    D.c-comp-assoc
    (D.c-trans (D.c-cong-comp (D.c-refl _) D.c-arr-fmap)
      (D.c-trans (D.c-sym D.c-comp-assoc)
        (D.c-trans (D.c-cong-comp (c-arrs-fmap k) (D.c-refl D.c-fmap))
                   D.c-comp-assoc)))

reify-mkcomp! :
  ∀ {a e b s e' t} →
  (ra : ty-rep s a) →
  (rb : ty-rep t b) →
  (re : ty-rep e' e) →
  (c : coe! a e) →
  (d : coe! e b) →
  reify! ra rb (mkcomp! c d) ≈ D.c-comp (reify! ra re c) (reify! re rb d)

reify-mkcomp' :
  ∀ {a e b s e' t} →
  (ra : ty-rep' s a) →
  (rb : ty-rep' t b) →
  (re : ty-rep' e' e) →
  (c : coe' a e) →
  (d : coe' e b) →
  reify' ra rb (mkcomp' c d) ≈ D.c-comp (reify' ra re c) (reify' re rb d)

reify-mkcomp-arr :
  {a b e f u v : ty'} →
  {a' b' e' f' u' v' a'' b'' u'' v'' : D.ty} →
  (k j : ℕ) →
  {na nb : ℕ} →
  {re : ty-rep' e' e} →
  {rf : ty-rep' f' f} →
  {ra : ty-rep' a' a} →
  {rb : ty-rep' b' b} →
  {ru : ty-rep' u' u} →
  {rv : ty-rep' v' v} →
  (c : coe' e a) →
  (c' : coe' b f) →
  (d : coe' u e) →
  (d' : coe' f v) →
  reify'
    (r-! na ra r-⇒ r-! nb rb)
    (r-! (j + (k + na)) ru r-⇒ r-! (j + (k + nb)) rv)
    (mkcomp-arr k j refl refl c c' d d') ≈
    let cc = reify' re ra c in
    let cc' = reify' rb rf c' in
    let dd = reify' ru re d in
    let dd' = reify' rf rv d' in
    D.c-comp (D.c-arr (c-monos na (D.c-comp dd cc)) (c-monos nb (D.c-comp cc' dd'))) (c-fmaps (j + k))

reify-mkcomp! {na ! a} {ne ! e} {nb ! b} {s} {e'} {t} ra rb re (c-! refl c) (c-! refl d)
    = heq_MAGIC

reify-mkcomp' {a} {e} {b} {s} {e'} {t} r-base r-base r-base c-base c-base
  = heq (D.c-sym D.c-id-l)

reify-mkcomp'
  {(na ! a) ⇒ (nb ! b)}
  {(ne ! e) ⇒ (nf ! f)}
  {(_ ! u) ⇒ (_ ! v)}
  {a' D.⇒ b'}
  {e' D.⇒ f'}
  {u' D.⇒ v'}
  ((r-! _ ra) r-⇒ (r-! _ rb))
  (r-! _ re r-⇒ r-! _ rf) (r-! _ ru r-⇒ r-! _ rv)
  (c-⇒ k (c-! refl c) (c-! refl d))
  (c-⇒ k' (c-! refl c') (c-! refl d')) =
  ≈-trans
    (reify-mkcomp-arr k k' c d c' d')
    (≈-trans
      (h-cong-comp
        (≈-trans
          (h-cong-arr (c-monos-comp na) (c-monos-comp nb))
          (heq D.c-arr-comp))
        (c-fmaps-+ k' k))
      (≈-trans
        (≈-trans
          (≈-trans
            (≈-trans
              (heq D.c-comp-assoc)
              (h-cong-comp
                (heq (D.c-refl _))
                (heq (D.c-sym D.c-comp-assoc))))
            (≈-sym (h-cong-comp (≈-refl _)
                     (≈-trans
                       (heq (D.c-sym D.c-comp-assoc))
                       (h-cong-comp (heq (c-arrs-fmap k)) (≈-refl _))))))
          (heq (D.c-sym D.c-comp-assoc)))
        (≈-sym
          (h-cong-comp
            (reify-arr k na nb c d)
            (≈-trans (reify-arr k' (k + na) (k + nb) c' d')
                     (h-cong-comp (h-cong-arr c-monos-+ c-monos-+) (h-fmaps-refl k' (fs-+ k na _) (fs-+ k nb _))))))))

reify-mkcomp-arr k zero {na} {nb} {re} {rf} {ra} {rb} {ru} {rv}
  c c' d d'
  = ≈-trans (reify-arr k na nb (mkcomp' d c) (mkcomp' c' d'))
            (h-cong-comp (h-cong-arr
              (c-monos-proper na refl refl (reify-mkcomp' ru ra _ d c ))
              (c-monos-proper nb refl refl (reify-mkcomp' rb rv _ c' d')))
              (≈-refl _))
reify-mkcomp-arr k (suc j) {na} {nb} c c' d d' =
  ≈-sym (≈-trans (heq (D.c-sym D.c-comp-assoc))
          (≈-trans
            (h-cong-comp
              (≈-sym (reify-mkcomp-arr k j c c' d d'))
              (h-fmap-refl
                (trans (fs-+ j k _) (sym (trans (fs-+ j (k + na) _) (cong (fs j) (fs-+ k na _)))))
                (trans (fs-+ j k _) (sym (trans (fs-+ j (k + nb) _) (cong (fs j) (fs-+ k nb _)))))))
            (≈-sym (heq (reify-mkfmap _ _ _ _)))))

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
reify-mkid' {base} {D.base} r-base r-base = D.c-refl (reify' r-base r-base (mkid' base))
reify-mkid' {(na ! a) ⇒ (nb ! b)} {s D.⇒ t} (ra r-⇒ rb) (ru r-⇒ rv) = {!!}

{-
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
