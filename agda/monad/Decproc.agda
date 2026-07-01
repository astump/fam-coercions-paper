module Decproc where

open import lib
open import Tp

data Flag : Set where
  Left : Flag
  Right : Flag
  Nothing : Flag

natFlagOk : 𝔹 → Flag → 𝔹 → Set
natFlagOk _ Left ff = ⊥
natFlagOk tt Nothing ff = ⊥
natFlagOk _ Right ff = ⊤
natFlagOk _ _ tt = ⊤
natFlagOk ff Nothing ff = ⊤

negFlag : Flag → Flag
negFlag Left = Right
negFlag Right = Left
negFlag Nothing = Nothing

funFlagOk : 𝔹 → Flag → 𝔹 → Flag → Set 
funFlagOk b f b' j = {!!}

-- The algorithmic coersion relation on normalized types
infix 5 _<_:!_
data _<_:!_ : Tp! → Flag → Tp! → Set where
  Nat! : ∀ {b b' : 𝔹}{f : Flag} →
          natFlagOk b f b' → 
          (b !N) < f :! (b' !N)

  Fun! : ∀ {b b' : 𝔹} {f j : Flag} {A B A' B' : Tp!} →
         A' < j :! A →
         B  < negFlag j :! B' →
         (b ! A ⇒ B) < f :! (b' ! A' ⇒ B')

natFlag-unique : ∀{b b' : 𝔹}{f : Flag} →
                  (x : natFlagOk b f b') →
                  (x' : natFlagOk b f b') →
                  x ≡ x'
natFlag-unique {tt} {tt} {Left} triv triv = refl
natFlag-unique {tt} {tt} {Right} triv triv = refl
natFlag-unique {tt} {tt} {Nothing} triv triv = refl
natFlag-unique {tt} {ff} {Left} () x'
natFlag-unique {tt} {ff} {Right} triv triv = refl
natFlag-unique {tt} {ff} {Nothing} () x'
natFlag-unique {ff} {tt} {Left} triv triv = refl
natFlag-unique {ff} {tt} {Right} triv triv = refl
natFlag-unique {ff} {tt} {Nothing} triv triv = refl
natFlag-unique {ff} {ff} {Left} () x'
natFlag-unique {ff} {ff} {Right} triv triv = refl
natFlag-unique {ff} {ff} {Nothing} triv triv = refl

uniqueness : ∀{A B : Tp!}{f : Flag} →
              (d1 : A < f :! B) →
              (d2 : A < f :! B) →
              d1 ≡ d2
uniqueness (Nat! x) (Nat! x₁) rewrite natFlag-unique x x₁ = refl
uniqueness (Fun! a a₁) (Fun! b b₁) = {!!}
{-
  -- Sequenced function rule (internalizes the Seq law)
  -- Does not require layerOK
  FunSeq! : ∀ {b b' : 𝔹} {A B A' B' : Tp!} →
           A'  <:! ↑ A →
           ↑ B <:! B' →
           (b ! A ⇒ B) <:! (b' ! A' ⇒ B')

{-
-- Reflexivity is admissible.
refl! : ∀ {A : Tp!} → A <:! A
refl! {ff !N}      = Nat! refl
refl! {tt !N}      = Nat! refl
refl! {ff ! A ⇒ B} = FunOrd! refl refl! refl!
refl! {tt ! A ⇒ B} = FunOrd! refl refl! refl!
-}
-}