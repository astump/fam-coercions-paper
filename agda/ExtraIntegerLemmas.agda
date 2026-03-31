-- TODO: Remove this when done!
{-# OPTIONS --allow-unsolved-metas #-}

open import lib

-- Helps avoid rewrites when Agda can't determine that b cannot be triv
mkℤ-onto : ∀{n m : ℕ}{b : 𝔹} → n ≡ m → mkℤ (suc n) b ≡ mkℤ (suc m) b
mkℤ-onto p rewrite p = refl

+ℤ-0 : ∀{x : ℤ} → x +ℤ 0ℤ ≡ x 
+ℤ-0 {mkℤ zero triv} = refl
+ℤ-0 {mkℤ (suc n) x} = refl

+ℤcomm : ∀{i j : ℤ} → i +ℤ j ≡ j +ℤ i
+ℤcomm {mkℤ zero triv}{j} = sym (+ℤ0{j})
+ℤcomm {mkℤ (suc n) tt} {mkℤ zero triv} = refl
+ℤcomm {mkℤ (suc n) tt} {mkℤ (suc m) tt} rewrite +suc m n | +suc n m | +comm n m = refl
+ℤcomm {mkℤ (suc n) tt} {mkℤ (suc m) ff} = refl
+ℤcomm {mkℤ (suc n) ff} {mkℤ zero triv} = refl
+ℤcomm {mkℤ (suc n) ff} {mkℤ (suc m) tt} = refl
+ℤcomm {mkℤ (suc n) ff} {mkℤ (suc m) ff} rewrite +suc m n | +suc n m | +comm n m = refl


toℤ-+ : ∀{n m : ℕ} → toℤ n +ℤ toℤ m ≡ toℤ (n + m) 
toℤ-+ {zero} {m} = refl
toℤ-+ {suc n} {zero} rewrite +0 n = refl
toℤ-+ {suc n} {suc m} = refl

diffℤ-0 : ∀{n : ℕ} → diffℤ n 0 ≡ toℤ n
diffℤ-0 {zero} = refl
diffℤ-0 {suc n} = refl

0-diffℤ : ∀{n : ℕ} → diffℤ 0 n ≡ negℤ (toℤ n)
0-diffℤ {zero} = refl
0-diffℤ {suc n} = refl

+1ℤ : ∀{n : ℕ} → toℤ (suc n) ≡ toℤ n +ℤ 1ℤ
+1ℤ {zero} = refl
+1ℤ {suc n} rewrite +1 n = refl

+-1ℤ : ∀{n : ℕ} → mkℤ (suc n) ff ≡ negℤ (toℤ n) +ℤ -1ℤ
+-1ℤ {zero} = refl
+-1ℤ {suc n} rewrite +1 n = refl

+ℤ-inv : ∀{x : ℕ} → (mkℤ (suc x) tt) +ℤ (mkℤ (suc x) ff) ≡ 0ℤ
+ℤ-inv {zero} = refl
+ℤ-inv {suc x} with ℕ-trichotomy (suc x) (suc x) | (<-irrefl (suc x))
+ℤ-inv {suc x} | inj₁ p | p2 with trans (sym p) p2
+ℤ-inv {suc x} | inj₁ p | p2 | () 
+ℤ-inv {suc x} | inj₂ (inj₂ p) | p2 with trans (sym p) p2
+ℤ-inv {suc x} | inj₂ (inj₂ p) | p2 | ()
+ℤ-inv {suc x} | inj₂ (inj₁ p) | p2 = refl

diffℤ-sucs : ∀{n m : ℕ} → diffℤ (suc n) (suc m) ≡ diffℤ n m
diffℤ-sucs {n} {m} with ℕ-trichotomy (suc n) (suc m) | ℕ-trichotomy n m
diffℤ-sucs {n} {m} | inj₁ p1 | inj₁ p2 with <∸suc{suc m}{suc n} p1 | <∸suc{m}{n} p2
diffℤ-sucs {n} {m} | inj₁ p1 | inj₁ p2 | x1 , e1 | x2 , e2 rewrite e1 = mkℤ-onto (suc-inj e2)
diffℤ-sucs {n} {m} | inj₂ (inj₂ p1) | inj₂ (inj₂ p2) with <∸suc{suc n}{suc m} p1 | <∸suc{n}{m} p2
diffℤ-sucs {n} {m} | inj₂ (inj₂ p1) | inj₂ (inj₂ p2) | x1 , e1 | x2 , e2 rewrite e1 = mkℤ-onto (suc-inj e2)
diffℤ-sucs {n} {m} | inj₂ (inj₁ p1) | inj₂ (inj₁ p2) = refl
diffℤ-sucs {n} {m} | inj₁ x | inj₂ (inj₁ p) rewrite =ℕ-to-≡{n}{m} p with trans (sym (<-irrefl m)) x
... | ()
diffℤ-sucs {n} {m} | inj₁ x | inj₂ (inj₂ p) with trans (sym (<-asym{n}{m} x)) p
... | ()
diffℤ-sucs {n} {m} | inj₂ (inj₁ x) | inj₁ p rewrite =ℕ-to-≡{n}{m} x with trans (sym (<-irrefl m)) p
... | ()
diffℤ-sucs {n} {m} | inj₂ (inj₁ x) | inj₂ (inj₂ p) rewrite =ℕ-to-≡{n}{m} x with trans (sym (<-irrefl m)) p
... | ()
diffℤ-sucs {n} {m} | inj₂ (inj₂ x) | inj₁ y with trans (sym (<-asym{n}{m} y)) x
... | ()
diffℤ-sucs {n} {m} | inj₂ (inj₂ x) | inj₂ (inj₁ y) rewrite =ℕ-to-≡{n}{m} y with trans (sym (<-irrefl m)) x
... | ()

diffℤ-nn : ∀{x : ℕ} → diffℤ x x ≡ 0ℤ
diffℤ-nn {zero} = refl
diffℤ-nn {suc x} rewrite diffℤ-sucs{x}{x} = diffℤ-nn{x}

+ℤ-cancel : ∀{x : ℤ} → x +ℤ negℤ x ≡ 0ℤ
+ℤ-cancel {mkℤ zero triv} = refl
+ℤ-cancel {mkℤ (suc n) tt} = diffℤ-nn{n}
+ℤ-cancel {mkℤ (suc n) ff} = diffℤ-nn{n}

+ℤ-cancel2 : ∀{x : ℤ} → negℤ x +ℤ x ≡ 0ℤ
+ℤ-cancel2{x} rewrite +ℤcomm{negℤ x}{x} = +ℤ-cancel{x}

diffℤ-suc : ∀{n m : ℕ} → diffℤ (suc n) m ≡ diffℤ n m +ℤ 1ℤ
diffℤ-suc {n} {zero} rewrite diffℤ-0{n} = +1ℤ
diffℤ-suc {zero} {suc m} = diffℤ-sucs{0}{m}
diffℤ-suc {suc n} {suc m} rewrite diffℤ-sucs{suc n}{m} | diffℤ-sucs{n}{m} = diffℤ-suc{n}{m}

-- diffℤ-+ : ∀{n m k : ℕ} → diffℤ (n + k) m ≡ diffℤ n m +ℤ toℤ k
-- diffℤ-+ {n} {m} {zero} rewrite +0 n = sym (+ℤ-0{diffℤ n m})
-- diffℤ-+ {n} {m} {suc k} = {!!}

+ℤ-assoc : ∀{x y z : ℤ} → (x +ℤ y) +ℤ z ≡ x +ℤ (y +ℤ z)
+ℤ-assoc {x} {mkℤ zero triv} {z} rewrite +ℤ0 {x} = refl
+ℤ-assoc {mkℤ zero triv} {mkℤ (suc m) tt} {z} = refl
+ℤ-assoc {mkℤ (suc n) tt} {mkℤ (suc m) tt} {mkℤ zero triv} = refl
+ℤ-assoc {mkℤ (suc n) tt} {mkℤ (suc m) tt} {mkℤ (suc k) tt}
  rewrite +assoc n (suc m) (suc k) = refl
+ℤ-assoc {mkℤ (suc n) tt} {mkℤ (suc m) tt} {mkℤ (suc k) ff} rewrite +suc n m | diffℤ-suc{n + m}{k} = {!!}
+ℤ-assoc {mkℤ (suc n) ff} {mkℤ (suc m) tt} {z} = {!!}
+ℤ-assoc {x} {mkℤ (suc n) ff} {z} = {!!}

≤ℤ-trans : ∀{x y z : ℤ} → x ≤ℤ y ≡ tt → y ≤ℤ z ≡ tt → x ≤ℤ z ≡ tt
≤ℤ-trans {x} {y} {z} p1 p2 = {!!}

≤ℤ-suc : ∀{n : ℕ} {b : 𝔹} → toℤ n ≤ℤ mkℤ (suc n) b ≡ b
≤ℤ-suc {zero} = refl
≤ℤ-suc {suc n} {tt} = ≤-suc n
≤ℤ-suc {suc n} {ff} = refl

≤ℤ-suc2 : ∀{n : ℕ} {b : 𝔹} → mkℤ (suc n) b ≤ℤ toℤ n ≡ ~ b
≤ℤ-suc2 {zero} = refl
≤ℤ-suc2 {suc n} {tt} = ≤-suc2 n
≤ℤ-suc2 {suc n} {ff} = refl

≤ℤ-diffℤ : ∀{n m : ℕ} → diffℤ n m ≤ℤ toℤ n ≡ tt
≤ℤ-diffℤ {zero} {zero} = refl
≤ℤ-diffℤ {zero} {suc m} = refl
≤ℤ-diffℤ {suc n} {zero} = ≤-refl n
≤ℤ-diffℤ {suc n} {suc m} rewrite diffℤ-sucs{n}{m} =
  ≤ℤ-trans{diffℤ n m} (≤ℤ-diffℤ{n}{m}) (≤ℤ-suc{n})

0-≤ℤ : ∀{n : ℕ} → 0ℤ ≤ℤ toℤ n ≡ tt
0-≤ℤ {zero} = refl
0-≤ℤ {suc n} = refl

≤ℤ-tt : ∀{n m : ℕ} → mkℤ (suc n) ff ≤ℤ toℤ m ≡ tt
≤ℤ-tt {m = zero} = refl
≤ℤ-tt {m = suc m} = refl

≤ℤ-ff : ∀{n m : ℕ} → toℤ n ≤ℤ mkℤ (suc m) ff ≡ ff
≤ℤ-ff {zero} = refl
≤ℤ-ff {suc n} = refl

≤ℤ-0-diffℤ : ∀{n m : ℕ} → diffℤ zero n ≤ℤ toℤ m ≡ tt
≤ℤ-0-diffℤ {zero} {m} rewrite diffℤ-0{zero} = 0-≤ℤ {m}
≤ℤ-0-diffℤ {suc n} {m} = ≤ℤ-tt{n}{m}

≤-≤ℤ : ∀{n m : ℕ} → n ≤ m ≡ toℤ n ≤ℤ toℤ m
≤-≤ℤ {zero} {zero} = refl
≤-≤ℤ {zero} {suc m} = refl
≤-≤ℤ {suc n} {zero} = refl
≤-≤ℤ {suc n} {suc m} = refl

negℤ-diffℤ : ∀{a b : ℕ} → diffℤ a b ≡ negℤ (diffℤ b a)
negℤ-diffℤ {zero} {zero} = refl
negℤ-diffℤ {suc a} {zero} = diffℤ-0{suc a}
negℤ-diffℤ {zero} {suc b} rewrite 0-diffℤ{suc b} = refl
negℤ-diffℤ {suc a} {suc b} rewrite diffℤ-sucs{a}{b} | diffℤ-sucs{b}{a} = negℤ-diffℤ{a}{b}

negℤ-≤ℤ : ∀{x y : ℤ} → x ≤ℤ y ≡ negℤ y ≤ℤ negℤ x
negℤ-≤ℤ {mkℤ zero triv} {mkℤ zero triv} = refl
negℤ-≤ℤ {mkℤ zero triv} {mkℤ (suc m) b} = sym (~~-elim b)
negℤ-≤ℤ {mkℤ (suc n) x} {mkℤ zero triv} = refl
negℤ-≤ℤ {mkℤ (suc n) tt} {mkℤ (suc m) tt} = refl
negℤ-≤ℤ {mkℤ (suc n) ff} {mkℤ (suc m) ff} = refl
negℤ-≤ℤ {mkℤ (suc n) tt} {mkℤ (suc m) ff} = refl
negℤ-≤ℤ {mkℤ (suc n) ff} {mkℤ (suc m) tt} = refl


diffℤ-≤ℤ-swap : ∀{a b c d : ℕ} → (diffℤ a b ≤ℤ diffℤ c d) ≡ (diffℤ d c ≤ℤ diffℤ b a)
diffℤ-≤ℤ-swap {a} {b} {c} {d}
  rewrite negℤ-diffℤ{d}{c}
        | negℤ-diffℤ{b}{a} = negℤ-≤ℤ{diffℤ a b}{diffℤ c d}

≤ℤ-1+ : ∀{x y : ℤ} → x ≤ℤ y ≡ x +ℤ 1ℤ ≤ℤ y +ℤ 1ℤ
≤ℤ-1+ {mkℤ zero triv} {mkℤ zero triv} = refl
≤ℤ-1+ {mkℤ zero triv} {mkℤ (suc n) tt} = sym (0-≤ (n + 1))
≤ℤ-1+ {mkℤ (suc n) tt} {mkℤ zero triv} rewrite +comm n 1 = refl
≤ℤ-1+ {mkℤ (suc n) tt} {mkℤ (suc m) tt} rewrite +comm n 1 | +comm m 1 = refl
≤ℤ-1+ {mkℤ (suc n) ff} {mkℤ zero triv} = sym (≤ℤ-0-diffℤ{n}{1})
≤ℤ-1+ {mkℤ (suc n) ff} {mkℤ (suc m) tt} = sym (≤ℤ-0-diffℤ{n}{suc (m + 1)})
≤ℤ-1+ {x} {mkℤ (suc n) ff}
  rewrite negℤ-≤ℤ{x +ℤ 1ℤ}{diffℤ 0 n}
        | sym (negℤ-diffℤ{n}{0})
        | diffℤ-0{n}
        = h x
  where h : ∀(x : ℤ) → x ≤ℤ mkℤ (suc n) ff ≡ toℤ n ≤ℤ negℤ (x +ℤ mkℤ 1 tt)
        h (mkℤ zero triv) = sym (≤ℤ-ff{n}{0})
        h (mkℤ (suc m) tt) = sym (≤ℤ-ff{n}{m + 1})
        h (mkℤ (suc m) ff) rewrite sym (negℤ-diffℤ{m}{0}) | diffℤ-0{m} = ≤-≤ℤ{n}{m}

≤ℤ+pm1 : ∀{x y : ℤ}{b : 𝔹} → x ≤ℤ y ≡ x +ℤ (mkℤ 1 b) ≤ℤ y +ℤ (mkℤ 1 b)
≤ℤ+pm1 {x} {y} {tt} = ≤ℤ-1+{x}{y}
≤ℤ+pm1 {x} {y} {ff}
  rewrite ≤ℤ-1+{x +ℤ -1ℤ}{y +ℤ -1ℤ}
        | +ℤ-assoc{x}{ -1ℤ }{1ℤ}
        | +ℤ-assoc{y}{ -1ℤ }{1ℤ}
        | +ℤ-0{x}
        | +ℤ-0{y} = refl

-- Helper to convince Agda of termination
≤ℤ-+help : ∀{x y : ℤ}(n : ℕ)(b : 𝔹) → x ≤ℤ y ≡ x +ℤ (mkℤ (suc n) b) ≤ℤ y +ℤ (mkℤ (suc n) b)
≤ℤ-+help {x} {y} zero b = ≤ℤ+pm1 {x} {y} {b}
≤ℤ-+help {x} {y} (suc n) tt 
  rewrite +1ℤ{suc n}
        | sym (+ℤ-assoc{x}{mkℤ (suc n) tt}{mkℤ 1 tt})
        | sym (+ℤ-assoc{y}{mkℤ (suc n) tt}{mkℤ 1 tt})
        | sym (≤ℤ+pm1{x +ℤ mkℤ (suc n) tt}{y +ℤ mkℤ (suc n) tt}{tt})
        = ≤ℤ-+help {x} {y} n tt
≤ℤ-+help {x} {y} (suc n) ff
  rewrite +-1ℤ{suc n}
        | sym (+ℤ-assoc{x}{mkℤ (suc n) ff}{mkℤ 1 ff})
        | sym (+ℤ-assoc{y}{mkℤ (suc n) ff}{mkℤ 1 ff})
        | sym (≤ℤ+pm1{x +ℤ mkℤ (suc n) ff}{y +ℤ mkℤ (suc n) ff}{ff})
        = ≤ℤ-+help {x} {y} n ff

≤ℤ-+ : ∀{x y : ℤ}(z : ℤ) → x ≤ℤ y ≡ x +ℤ z ≤ℤ y +ℤ z
≤ℤ-+ {x} {y} (mkℤ zero triv) rewrite +ℤ-0{x} | +ℤ-0{y} = refl
≤ℤ-+ {x} {y} (mkℤ (suc n) b) = ≤ℤ-+help {x} {y} n b

≤ℤ-+2 : ∀{x y : ℤ}(z : ℤ) → x ≤ℤ y ≡ z +ℤ x ≤ℤ z +ℤ y
≤ℤ-+2 {x} {y} z rewrite +ℤcomm{z}{x} | +ℤcomm{z}{y} = ≤ℤ-+{x}{y} z

≤ℤ-+2a : ∀{x y : ℤ}{z : ℤ} → x ≤ℤ y ≡ tt → z +ℤ x ≤ℤ z +ℤ y ≡ tt
≤ℤ-+2a{x}{y}{z} e = sym (trans (sym e) ((≤ℤ-+2 z)))

negℤ-+ : ∀{x y : ℤ} → negℤ (x +ℤ y) ≡ negℤ x +ℤ negℤ y
negℤ-+ = {!!}

≤ℤ+ : ∀{x y z : ℤ} → x ≤ℤ y ≡ tt → x ≤ℤ z ≡ tt → x ≤ℤ (y +ℤ z) ≡ tt
≤ℤ+ = {!!}


≤ℤ+2 : ∀{x y x' y' : ℤ} → x ≤ℤ x' ≡ tt → y ≤ℤ y' ≡ tt → x +ℤ y ≤ℤ x' +ℤ y' ≡ tt
≤ℤ+2 = {!!}