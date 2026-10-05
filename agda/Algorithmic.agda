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

≡-to-≤ℤ : {j k : ℤ} →
  j ≡ k →
  j ≤ℤ k ≡ tt
≡-to-≤ℤ {j} refl = (≤ℤ-refl {j})

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
  Fun {-j = negℤ k-} (trans (sym (negℤ-≤ℤ {k} {0ℤ})) kbd) {!!} ua' bv'

complete-fun-helper : {n mm m j k j' k' : ℤ} →
  j ≤ℤ j' ≡ tt →
  k ≤ℤ negℤ j' ≡ tt →
  n +ℤ negℤ mm +ℤ negℤ m ≤ℤ j' ≡ tt →
  k +ℤ n -ℤ m ≤ℤ mm ≡ tt
complete-fun-helper {n} {mm} {m} {j} {k} {j'} {k'} pj pk pf =
  let pf' = ≤-add-cancel-fwd {n +ℤ negℤ mm +ℤ negℤ m} {j'} (mm -ℤ j') pf in
  let cc = (cong2 {_} {_} {_} {_} {_} {_}
          {k +ℤ n -ℤ m}
          { n +ℤ negℤ mm +ℤ negℤ m +ℤ (mm -ℤ j')}
          {mm}
          { j' +ℤ (mm -ℤ j')}
          (λ x y → x ≤ℤ y) {!!} {!!}) in
  trans cc pf'

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

algo-uniq : {a b : Tp!} {j k : ℤ} →
  a <[ j ] b →
  a <[ k ] b →
  j ≡ k
algo-uniq {a} {b} {j} {k} s-nat s-nat = refl
algo-uniq {n ! a ⇒ b} {m ! u ⇒ v} {j} {k}
  (s-fun pua pbv pk pjk)
  (s-fun pua' pbv' pk' pjk')
  rewrite algo-uniq pbv pbv' = refl
