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

fs-comm : (n : ℕ) → (a : D.ty) → fs n (D.f a) ≡ D.f (fs n a)
fs-comm 0 a = refl
fs-comm (suc n) a rewrite fs-comm n a = refl

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

eval-ty!-r : (n : ℕ) → (a : D.ty) → Σ[ t ∈ ty! ] ty-rep (fs n a) t
eval-ty!-r n (D.f a) rewrite (fs-comm n a) =
  eval-ty!-r (suc n) a
eval-ty!-r n D.base = n ! base , r-fs n r-base
eval-ty!-r n (a D.⇒ b) =
  let ta , ra = eval-ty!-r 0 a in
  let tb , rb = eval-ty!-r 0 b in
  n ! ta ⇒ tb , r-fs n (ra r-⇒ rb)

eval-ty-r : (a : D.ty) → Σ[ t ∈ ty! ] ty-rep a t
eval-ty-r = eval-ty!-r 0

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

eval-reify-ty : (t : ty!) → eval-ty (reify-ty t) ≡ t
eval-reify-ty t with reify-ty-r t
...                | a , ra with eval-ty-r a
...                            | b , rb = ty-rep-inj₂ rb ra


reify-eval-ty : (t : D.ty) → reify-ty (eval-ty t) ≡ t
reify-eval-ty t with eval-ty-r t
...                | a , ra with reify-ty-r a
...                            | b , rb = ty-rep-inj₁ rb ra
