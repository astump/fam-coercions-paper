module Uniqueness where

open import lib
open import Tp
open import Decproc


uniqueness : ∀{A B : Tp!}{f : Flag} →
              (d1 : A < f :! B) →
              (d2 : A < f :! B) →
              d1 ≡ d2
uniqueness (Nat! x) (Nat! x₁) rewrite natFlag-unique x x₁ = refl
uniqueness (Fun! {b1}{b1'}{f1}{Right} x a b) (Fun! {b2}{b2'}{j = Right} x₁ a₁ b₁)
  rewrite funFlag-unique{b1}{b1'}{f1}{Right} x x₁ | uniqueness a a₁ | uniqueness b b₁
  = refl
-- The two mixed cases below should be impossible because funFlagOK with j=Nothing never equals
-- funFlagOk with j=Right (both cannot be valad). I need to write a lemma for this.
uniqueness (Fun! {b1} {b1'} {f1} {j = Nothing} x a b) (Fun! {j = Right} x₁ a₁ b₁)
  -- rewrite uniqueness a a₁
  -- funFlag-unique {b1} {b1'} {f1} x x₁ | uniqueness a a₁ | uniqueness b b₁
  = {!!}
uniqueness (Fun! {j = Right} x a b) (Fun! {j = Nothing} x₁ a₁ b₁)
  -- rewrite funFlag-unique x x₁ | uniqueness a a₁ | uniqueness b b₁
  = {!!}
uniqueness (Fun! {j = Nothing} x a b) (Fun! {j = Nothing} x₁ a₁ b₁)
  rewrite funFlag-unique x x₁ | uniqueness a a₁ | uniqueness b b₁
  = refl
{-
-- Reflexivity is admissible.
refl! : ∀ {A : Tp!} → A <:! A
refl! {ff !N}      = Nat! refl
refl! {tt !N}      = Nat! refl
refl! {ff ! A ⇒ B} = FunOrd! refl refl! refl!
refl! {tt ! A ⇒ B} = FunOrd! refl refl! refl!
-}
