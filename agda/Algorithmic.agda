open import lib
open import Tp
open import Decproc
open import ExtraIntegerLemmas

infix 5 _<[_]_
data _<[_]_ : Tp! → ℤ → Tp! → Set where
  s-nat : ∀ {n m : ℕ} →
    n !N <[ toℤ n -ℤ toℤ m ] m !N
  s-fun : ∀ {n m : ℕ} {j k : ℤ} {a b u v : Tp!} →
    u <[ j ] a →
    b <[ k ] v →
    k ≤ℤ 0ℤ ≡ tt →
    j ≤ℤ negℤ k ≡ tt →
    n ! a ⇒ b <[ k +ℤ toℤ n -ℤ toℤ m ] m ! u ⇒ v

j≡j+k-k : ∀ (j k : ℤ) → j ≡ j +ℤ k -ℤ k
j≡j+k-k j k
  rewrite +ℤ-assoc {j} {k} {negℤ k}
        | +ℤ-cancel {k}
        | +ℤ-0 {j} = refl

j≡j-k+k : ∀ (j k : ℤ) → j ≡ j -ℤ k +ℤ k
j≡j-k+k j k
  rewrite +ℤ-assoc {j} {negℤ k} {k}
        | +ℤ-comm {negℤ k} {k}
        | +ℤ-cancel {k}
        | +ℤ-0 {j} = refl

≤-add-cancel : {j k : ℤ} (l : ℤ) →
 j ≤ℤ k ≡ j +ℤ l ≤ℤ k +ℤ l
≤-add-cancel {j} {k} l
  rewrite ≤ℤ-+2 {j} {k} l
        | +ℤ-comm {k} {l}
        | +ℤ-comm {j} {l}
        = refl

≤-add-cancel-fwd : {j k : ℤ} (l : ℤ) →
 j ≤ℤ k ≡ tt →
 j +ℤ l ≤ℤ k +ℤ l ≡ tt
≤-add-cancel-fwd {j} {k} l pf
  rewrite ≤-add-cancel {j} {k} l = pf

≤-add-cancel-bwd : {j k : ℤ} (l : ℤ) →
 j +ℤ l ≤ℤ k +ℤ l ≡ tt →
 j ≤ℤ k ≡ tt
≤-add-cancel-bwd {j} {k} l pf
  rewrite ≤-add-cancel {j} {k} l = pf


arith-knmkk : {k n m kk : ℤ} →
  k +ℤ n -ℤ m ≤ℤ kk ≡ tt →
  negℤ k ≥ℤ n -ℤ kk -ℤ m ≡ tt
arith-knmkk {k} {n} {m} {kk} pf
  rewrite negℤ-≤ℤ {k +ℤ n -ℤ m} {kk}
        | negℤ-+ {k +ℤ n} {negℤ m}
        | negℤ-+ {k} {n}
        | negℤ-invol {m}
        | ≤ℤ-+ {negℤ kk} {negℤ k +ℤ negℤ n +ℤ m} (negℤ m)
        | +ℤ-assoc {negℤ k +ℤ negℤ n} {m} {negℤ m}
        | +ℤ-cancel {m}
        | +ℤ0 {negℤ k +ℤ negℤ n}
        | +ℤ-comm {negℤ k} {negℤ n}
        | ≤ℤ-+2 {negℤ kk +ℤ negℤ m} {negℤ n +ℤ negℤ k} n
        | sym (+ℤ-assoc {n} {negℤ n} {negℤ k})
        | +ℤ-cancel {n}
        | +ℤ-assoc {n} {negℤ kk} {negℤ m}
  = pf

sound : {k j : ℤ} {a b : Tp!} →
  k ≤ℤ j ≡ tt →
  a <[ k ] b →
  a < j ] b
sound {k} {j} {n !N} {m !N} kj s-nat =
  let ii = toℤ n +ℤ negℤ (toℤ m) +ℤ toℤ m in
  NatRefl
    (≤ℤ-trans {toℤ n} {ii} {j +ℤ toℤ m}
      (≡-to-≤ℤ {toℤ n} {ii} (j≡j-k+k (toℤ n) (toℤ m)))
      (trans (sym (≤-add-cancel {toℤ n -ℤ toℤ m} {j} (toℤ m))) kj))
sound {jj} {kk} {n ! a ⇒ b} {m ! u ⇒ v} kj
  (s-fun {n} {m} {j} {k} pua pbv kbd jbd) =
  let ua' = sound jbd pua in
  let bv' = sound (≡-to-≤ℤ (sym (negℤ-invol{k}))) pbv in
  let pf = arith-knmkk {k} {toℤ n} {toℤ m} {kk} kj in
  Fun (trans (sym (negℤ-≤ℤ {k} {0ℤ})) kbd) pf ua' bv'

useful-swap : ∀ {n mm m j'} →
  n +ℤ negℤ mm +ℤ m ≤ℤ j' ≡ tt →
  negℤ j' +ℤ (n +ℤ m) ≤ℤ mm ≡ tt
useful-swap {n} {mm} {m} {j'} pf
  rewrite +ℤ-comm {n} {negℤ mm}
        | +ℤ-assoc {negℤ mm} {n} {m}
        | ≤ℤ-+2 {negℤ mm +ℤ (n +ℤ m)} {j'} mm
        | sym (+ℤ-assoc {mm} {negℤ mm} {n +ℤ m})
        | +ℤ-cancel {mm}
        | ≤ℤ-+2 {negℤ j' +ℤ (n +ℤ m)} {mm} j'
        | sym (+ℤ-assoc {j'} {negℤ j'} {n +ℤ m})
        | +ℤ-cancel {j'}
        | +ℤ-comm {j'} {mm}
  = pf

complete-fun-helper : {n mm m j k j' k' : ℤ} →
  j ≤ℤ j' ≡ tt →
  k ≤ℤ negℤ j' ≡ tt →
  n +ℤ negℤ mm +ℤ negℤ m ≤ℤ j' ≡ tt →
  k +ℤ n -ℤ m ≤ℤ mm ≡ tt
complete-fun-helper {n} {mm} {m} {j} {k} {j'} {k'} pj pk pf =
  ≤ℤ-trans
    {k +ℤ n -ℤ m}
    {k +ℤ (n -ℤ m)}
    {mm}
    (≡-to-≤ℤ
      {k +ℤ n -ℤ m}
      {k +ℤ (n -ℤ m)}
      (+ℤ-assoc {k} {n} {negℤ m}))
    (≤ℤ-trans
        {k +ℤ (n -ℤ m)}
        {negℤ j' +ℤ (n -ℤ m)}
        {mm}
        (≤ℤ-+1 {k} {negℤ j'} {n -ℤ m} pk)
        (useful-swap {n} {mm} {negℤ m} {j'} pf))

≤ℤ-swap : {j k : ℤ} →
  k ≤ℤ j ≡ tt →
  negℤ j ≤ℤ negℤ k ≡ tt
≤ℤ-swap {j} {k} pkj
  rewrite negℤ-≤ℤ {k} {j} = pkj

complete : {j : ℤ} {a b : Tp!} →
  a < j ] b →
  Σ[ k ∈ ℤ ] k ≤ℤ j ≡ tt × a <[ k ] b
complete {j} {n !N} {m !N} (NatRefl k) =
  toℤ n -ℤ toℤ m ,
  trans
    (cong (λ e → toℤ n +ℤ negℤ (toℤ m) ≤ℤ e) (j≡j+k-k _ _))
    (trans
      (sym (≤-add-cancel {toℤ n} {j +ℤ toℤ m} (negℤ (toℤ m))))
      k) ,
  s-nat
complete {mm} {n ! a ⇒ b} {m ! u ⇒ v} (Fun {n'} {m'} {j'} {k'} pj0 pnkm pua pbv)
  with complete pua | complete pbv
...  | j , pj , ua' | k , pk , bv' =
  let nn = k +ℤ toℤ n -ℤ toℤ m in
  nn ,
  complete-fun-helper {toℤ n} {mm} {toℤ m} {j} {k} {j'} {k'} pj pk pnkm ,
  s-fun ua' bv'
    (≤ℤ-trans {k} {negℤ j'} {0ℤ} pk (≤ℤ-swap {j'} {0ℤ} pj0))
    (≤ℤ-trans {j} {j'} {negℤ k}
      pj
      (≤ℤ-trans {j'} {negℤ (negℤ j')} {negℤ k}
        (≡-to-≤ℤ (sym (negℤ-invol{j'})))
        (≤ℤ-swap {negℤ j'} {k} pk)))

infix 5 _<[_]'_
data _<[_]'_ : Tp! → ℤ → Tp! → Set where
  s-nat : ∀ {n m : ℕ} →
    n !N <[ toℤ n -ℤ toℤ m ]' m !N
  s-fun : ∀ {n m : ℕ} {j k i : ℤ} {a b u v : Tp!} →
    u <[ j ]' a →
    b <[ k ]' v →
    k ≤ℤ 0ℤ ≡ tt →
    j ≤ℤ negℤ k ≡ tt →
    i ≡ k +ℤ toℤ n -ℤ toℤ m →
    n ! a ⇒ b <[ i ]' m ! u ⇒ v

algo-uniq : {a b : Tp!} {j k : ℤ} →
  a <[ j ]' b →
  a <[ k ]' b →
  j ≡ k
algo-uniq {a} {b} {j} {k} s-nat s-nat = refl
algo-uniq {n ! a ⇒ b} {m ! u ⇒ v} {j} {k}
  (s-fun pua pbv pk pjk refl)
  (s-fun pua' pbv' pk' pjk' refl)
  rewrite algo-uniq pbv pbv' = refl

leq-uniq : ∀ {a b} →
  (p : a ≤ℤ b ≡ tt) →
  (q : a ≤ℤ b ≡ tt) →
  p ≡ q
leq-uniq p q rewrite p | q = refl

algo-uniq' : {a b : Tp!} {k : ℤ} →
  (c : a <[ k ]' b) →
  (d : a <[ k ]' b) →
  c ≡ d
algo-uniq' {x !N} {x₁ !N} {k} s-nat s-nat = refl
algo-uniq' {x !N} {x₁ ! b ⇒ b₁} {k} () d
algo-uniq' {x ! a ⇒ a₁} {x₁ !N} {k} () d
algo-uniq' {n ! a ⇒ b} {m ! u ⇒ v} {k}
  (s-fun {n1} {m1} {j1} {k1} c d pk pjk pi)
  (s-fun {n2} {m2} {j2} {k2}  c' d' pk' pjk' pi')
  with algo-uniq c c' | algo-uniq d d'
... | refl | refl
  with algo-uniq' c c' | algo-uniq' d d'
... | refl | refl
  rewrite pi' | pi =
  cong2 (λ p q → s-fun c d p q refl)
    (leq-uniq {k1} {mkℤ 0 triv} pk pk')
    (leq-uniq {j1} {negℤ k1} pjk pjk')
