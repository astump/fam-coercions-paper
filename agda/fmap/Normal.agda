module fmap.Normal where
open import Relation.Binary.PropositionalEquality
open import Data.Product
import fmap.Decl as D

data coe : D.ty → D.ty → Set
data coe-arr : D.ty × D.ty → D.ty × D.ty → Set
data coe where
  c-id : coe D.base D.base
  c-mono : ∀ {a b} → coe a b → coe (D.f a) (D.f b)
  c-arr : ∀ {a b u v} → coe-arr (a , b) (u , v) → coe (a D.⇒ b) (u D.⇒ v)
data coe-arr where
  ca-arr : ∀ {a b u v} → coe u a → coe b v → coe-arr (a , b) (u , v)
  ca-fmap : ∀ {a b u v} → coe-arr (a , b) (u , v) → coe-arr (a , b) (D.f u , D.f v)
