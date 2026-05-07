module Semantics where

open import lib
open import Tp
open import Declarative
open import Decproc

infix 7 ⟦_⟧ 

⟦_⟧ : Tp! → Tp
⟦ l !N ⟧ = constrL l N
⟦ l ! T1 ⇒ T2 ⟧ = constrL l (⟦ T1 ⟧ ⇒ ⟦ T2 ⟧)

infix 6 ⊨_<]_

⊨_<]_ : Tp! → Tp! → Set
⊨ T1 <] T2 = ⟦ T1 ⟧ <: ⟦ T2 ⟧
