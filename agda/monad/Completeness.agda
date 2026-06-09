module Completeness where

open import lib
open import Tp
open import Declarative
open import Decproc
open import Semantics
open import DecprocTrans

-- Completeness helpers

-- completeness for pure
pure! : ∀ {A : Tp!} → A <:! ↑ A
pure! {ff !N} = Nat<! refl
pure! {tt  !N} = Nat<! refl
pure! {ff ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl <:!-refl
pure! {tt ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl <:!-refl

-- completeness for join
join! : ∀ {A : Tp!} → ↑ (↑ A) <:! ↑ A
join! {ff !N} = Nat<! refl
join! {tt  !N} = Nat<! refl
join! {ff ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl <:!-refl
join! {tt ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl <:!-refl

-- completeness for seq
seq! : ∀ {A B : Tp!} →
       (tt ! A ⇒ B) <:! (ff ! ↑ A ⇒ ↑ B)
seq! =
  Fun<! {q = tt}
        refl
        <:!-refl
        <:!-refl

-- Full completeness
complete! : ∀ {A B : Tp} → A <: B → ⌈ A ⌉ <:! ⌈ B ⌉
complete! NatRefl =
  Nat<! refl

complete! (Fun dom cod) =
  Fun<! {q = ff} refl
        (complete! dom)
        (complete! cod)

complete! Seq =
  seq!

complete! Pure =
  pure!

complete! (Cov p) =
  cov! (complete! p)

complete! Join =
  join!

complete! (Trans p q) =
  trans! {size (complete! p) + size (complete! q)}
         (complete! p)
         (complete! q)
         (≤-refl (size (complete! p) + size (complete! q)))
