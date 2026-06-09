module Decproc where

open import lib
open import Tp

-- the only impossible coercion is L T <: T
layerOK : 𝔹 → 𝔹 → 𝔹
layerOK tt ff = ff
layerOK _ _ = tt

-- function-rule outer condition
funOK : 𝔹 → 𝔹 → 𝔹 → 𝔹
funOK ff b b' = layerOK b b'
funOK tt b b' = tt

funOK-tt-tt : ∀{q b : 𝔹} → funOK q b tt ≡ tt
funOK-tt-tt {tt} {b} = refl
funOK-tt-tt {ff} {tt} = refl
funOK-tt-tt {ff} {ff} = refl

-- ---------------------------------------------------------------------------
-- algorithmic relation on Tp!
infix 5 _<:!_

data _<:!_ : Tp! → Tp! → Set where
  Nat<! : ∀ {b b' : 𝔹} →
          layerOK b b' ≡ tt →
          (b !N) <:! (b' !N)

  {- Function rule

  if q = ff, this is the ordinary function rule.
  Input
    A' <:! A
    B  <:! B'
  Output
    b! A ⇒ B <:! b'! A' ⇒ B'
    so long as  ¬(b ≡ T ∧ b' ≡ F)

  If q = tt, this is a Seq-shaped rule.
  Input
    A'  <:! ↑ A
    ↑ B <:! B'
  Output
    b! A ⇒ B <:! b'! A' ⇒ B'
    For all b b'
  -}
  Fun<! : ∀ {q b b' : 𝔹}
           {A B A' B' : Tp!} →
          funOK q b b' ≡ tt →
          A' <:! bump! q A →
          bump! q B <:! B' →
          (b ! A ⇒ B) <:! (b' ! A' ⇒ B')

-- Reflexivity is admissible
<:!-refl : ∀ {A : Tp!} → A <:! A
<:!-refl {ff !N} = Nat<! refl
<:!-refl {tt  !N} = Nat<! refl
<:!-refl {ff ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl (<:!-refl {A = B})
<:!-refl {tt  ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl (<:!-refl {A = B})
