module Uniqueness where

open import lib
open import Tp
open import Decproc

ord-seq-disjoint : ∀{b b' : 𝔹}{f : Flag} →
                   funFlagOk b f b' Ord →
                   funFlagOk b f b' Seq →
                   ⊥{lzero}
ord-seq-disjoint {tt} {tt} {f = Left} _ ()
ord-seq-disjoint {tt} {ff} {f = Left} ()
ord-seq-disjoint {ff} {tt} {f = Left} _ ()
ord-seq-disjoint {ff} {ff} {f = Left} ()
ord-seq-disjoint {tt} {b'} {f = Right} _ ()
ord-seq-disjoint {ff} {b'} {f = Right} _ ()
ord-seq-disjoint {tt} {tt} {f = Nothing} _ ()
ord-seq-disjoint {tt} {ff} {f = Nothing} ()
ord-seq-disjoint {ff} {b'} {f = Nothing} _ ()

seq-ord-disjoint : ∀{b b' : 𝔹}{f : Flag} →
                   funFlagOk b f b' Seq →
                   funFlagOk b f b' Ord →
                   ⊥
seq-ord-disjoint x y = ord-seq-disjoint y x


uniqueness : ∀{A B : Tp!}{f : Flag} →
              (d1 : A < f :! B) →
              (d2 : A < f :! B) →
              d1 ≡ d2
uniqueness (Nat! x) (Nat! x₁) rewrite natFlag-unique x x₁ = refl
uniqueness (Fun! {b1}{b1'}{f1}{Seq} x a b) (Fun! {b2}{b2'}{j = Seq} x₁ a₁ b₁)
  rewrite funFlag-unique {b1} {b1'} {f1} {Seq} x x₁ | uniqueness a a₁ | uniqueness b b₁
  = refl
-- Mixed mode cases are impossible by construction
uniqueness (Fun! {b1} {b1'} {f1} {j = Ord} x a b) (Fun! {j = Seq} x₁ a₁ b₁)
  = ⊥-elim (ord-seq-disjoint {b1} {b1'} {f1} x x₁)
uniqueness (Fun! {b1} {b1'} {f1} {j = Seq} x a b) (Fun! {j = Ord} x₁ a₁ b₁)
  = ⊥-elim (seq-ord-disjoint {b1} {b1'} {f1} x x₁)
uniqueness (Fun! {j = Ord} x a b) (Fun! {j = Ord} x₁ a₁ b₁)
  rewrite funFlag-unique x x₁ | uniqueness a a₁ | uniqueness b b₁
  = refl
