module Decproc where

open import lib
open import Tp

data Flag : Set where
  Left : Flag
  Right : Flag
  Nothing : Flag

-- everything is good but tt <: ff
natFlagOk : 𝔹 → Flag → 𝔹 → Set
natFlagOk _ _ tt = ⊤
natFlagOk _ Left ff = ⊥
natFlagOk _ Right ff = ⊤
natFlagOk tt Nothing ff = ⊥
natFlagOk ff Nothing ff = ⊤

negFlag : Flag → Flag
negFlag Left = Right
negFlag Right = Left
negFlag Nothing = Nothing

funFlagOk : 𝔹 → Flag → 𝔹 → Flag → Set
-- j = Nothing : ordinary Fun rule.
funFlagOk b f b' Nothing = natFlagOk b f b'
-- j = Right : sequenced Fun rule.
-- ONLY on the 3 cells FunOrd misses to prevent overlap
--     (tt , Nothing , ff)  —  L(A⇒B) <: (A'⇒B') via Seq then Fun
--     (_  , Left    , ff)
funFlagOk tt Nothing ff Right = ⊤
funFlagOk _  Left    ff Right = ⊤
funFlagOk _  _       _  Right = ⊥
-- j = Left
-- Every cell it could reach is already acheviable by Fun Ord
funFlagOk _  _       _  Left  = ⊥

-- The algorithmic coersion relation on normalized types
infix 5 _<_:!_
data _<_:!_ : Tp! → Flag → Tp! → Set where
  Nat! : ∀ {b b' : 𝔹}{f : Flag} →
          natFlagOk b f b' → 
          (b !N) < f :! (b' !N)

  Fun! : ∀ {b b' : 𝔹} {f j : Flag} {A B A' B' : Tp!} →
         funFlagOk b f b' j →
         A' < j :! A →
         B  < negFlag j :! B' →
         (b ! A ⇒ B) < f :! (b' ! A' ⇒ B')

natFlag-unique : ∀{b b' : 𝔹}{f : Flag} →
                  (x  : natFlagOk b f b') →
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

funFlag-unique : ∀{b b' : 𝔹}{f j : Flag} →
                  (x  : funFlagOk b f b' j) →
                  (x' : funFlagOk b f b' j) →
                  x ≡ x'
funFlag-unique {j = Nothing} x x' = natFlag-unique x x'
funFlag-unique {tt} {ff} {Nothing} {Right} triv triv = refl
funFlag-unique {tt} {ff} {Left} {Right} triv triv = refl
funFlag-unique {ff} {ff} {Left}  {Right} triv triv = refl

