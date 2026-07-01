module Tp where

open import lib

-- Source types for the declarative `_<:_` relation
data Tp : Set where
  N   : Tp              -- base type
  L_  : Tp → Tp         -- monad layer
  _⇒_ : Tp → Tp → Tp    -- functions

infixr 9 _⇒_
infixr 10 L_

-- Normalized types for the decproc `_<:!_` relation
-- `Tp!` collapses `L`s into one boolean flag.
-- ff means "no Ls", tt means "at least one L"
-- This is justified because pure/join make L (L T) ≈ L T.
data Tp! : Set where
  _!N   : 𝔹 → Tp!
  _!_⇒_ : 𝔹 → Tp! → Tp! → Tp!

infixr 9 _!_⇒_
infixr 10 _!N

-- Force the layer bit to tt.
infix 30 ↑_
↑_ : Tp! → Tp!
↑ (_ !N)      = tt !N
↑ (_ ! A ⇒ B) = tt ! A ⇒ B
