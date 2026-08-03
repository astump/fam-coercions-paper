module Decproc where

open import lib
open import Tp

data Flag : Set where
  Left : Flag
  Right : Flag
  Nothing : Flag

-- Internal mode for function coercions.
-- Ord uses the ordinary function rule, Seq uses the sequenced rule.
data FunMode : Set where
  Ord : FunMode
  Seq : FunMode

domFlag : FunMode → Flag
domFlag Ord = Nothing
domFlag Seq = Right

codFlag : FunMode → Flag
codFlag Ord = Nothing
codFlag Seq = Left

-- everything is good but tt <: ff
natFlagOk : 𝔹 → Flag → 𝔹 → Set
natFlagOk _ Left ff = ⊥
natFlagOk tt Nothing ff = ⊥
natFlagOk _ _ _ = ⊤


funFlagOk : 𝔹 → Flag → 𝔹 → FunMode → Set
-- Ord mode follows natFlagOk.
funFlagOk b f b' Ord = natFlagOk b f b'
-- Seq mode is intentionally enabled only on cells where Ord is impossible.
-- This artificial partition prevents overlap between the two function-rule
-- interpretations and gives a canonical derivation choice per cell.
-- The enabled Seq-only cells are:
--   (tt , Nothing , ff)  -- L(A⇒B) <: (A'⇒B') via Seq then Fun
--   (_  , Left    , ff)
funFlagOk tt Nothing ff Seq = ⊤
funFlagOk _  Left    ff Seq = ⊤
funFlagOk _  _       _  Seq = ⊥

-- The algorithmic coersion relation on normalized types
infix 5 _<_:!_
data _<_:!_ : Tp! → Flag → Tp! → Set where
  Nat! : ∀ {b b' : 𝔹}{f : Flag} →
          natFlagOk b f b' → 
          (b !N) < f :! (b' !N)

  Fun! : ∀ {b b' : 𝔹} {f : Flag} {j : FunMode} {A B A' B' : Tp!} →
         funFlagOk b f b' j →
      A' < domFlag j :! A →
      B  < codFlag j :! B' →
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

funFlag-unique : ∀{b b' : 𝔹}{f : Flag}{j : FunMode} →
                  (x  : funFlagOk b f b' j) →
                  (x' : funFlagOk b f b' j) →
                  x ≡ x'
funFlag-unique {j = Ord} x x' = natFlag-unique x x'
funFlag-unique {tt} {ff} {Nothing} {Seq} triv triv = refl
funFlag-unique {tt} {ff} {Left} {Seq} triv triv = refl
funFlag-unique {ff} {ff} {Left}  {Seq} triv triv = refl

