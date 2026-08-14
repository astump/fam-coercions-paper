module Decproc where

open import lib
open import Tp

data Flag : Set where
  Left : Flag
  Right : Flag
  Nothing : Flag

-- Toggles the function rule between ordinary and sequenced
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

-- Top L-bit of a normalized type.
topBit : Tp! → 𝔹
topBit (b !N)      = b
topBit (b ! _ ⇒ _) = b

funFlagOk : 𝔹 → Flag → 𝔹 → FunMode → 𝔹 → 𝔹 → Set
-- Ord mode 
funFlagOk b f b' Ord da' da = natFlagOk b f b' ∧ natFlagOk da' Nothing da
-- Seq mode
funFlagOk tt Nothing ff Seq _  _  = ⊤
funFlagOk _  Left    ff Seq _  _  = ⊤
funFlagOk ff Nothing ff Seq tt ff = ⊤
funFlagOk _  _       _  Seq _  _  = ⊥

-- The algorithmic coersion relation on normalized types
infix 5 _<_:!_
data _<_:!_ : Tp! → Flag → Tp! → Set where
  Nat! : ∀ {b b' : 𝔹}{f : Flag} →
          natFlagOk b f b' → 
          (b !N) < f :! (b' !N)

  Fun! : ∀ {b b' : 𝔹} {f : Flag} {j : FunMode} {A B A' B' : Tp!} →
           funFlagOk b f b' j (topBit A') (topBit A) →
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

funFlag-unique : ∀{b b' : 𝔹}{f : Flag}{j : FunMode}{da' da : 𝔹} →
                  (x  : funFlagOk b f b' j da' da) →
                  (x' : funFlagOk b f b' j da' da) →
                  x ≡ x'
funFlag-unique {j = Ord} (x1 , x2) (x1' , x2')
  rewrite natFlag-unique x1 x1' | natFlag-unique x2 x2' = refl
funFlag-unique {tt} {ff} {Nothing} {Seq} triv triv = refl
funFlag-unique {tt} {ff} {Left} {Seq} triv triv = refl
funFlag-unique {ff} {ff} {Left}  {Seq} triv triv = refl
funFlag-unique {ff} {ff} {Nothing} {Seq} {tt} {ff} triv triv = refl

