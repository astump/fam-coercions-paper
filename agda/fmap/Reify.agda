module fmap.Reify where
open import Relation.Binary.PropositionalEquality
open import Data.Product
import fmap.Algo as A
import fmap.Decl as D
import fmap.Normal as N
open import fmap.TypeIso

-- reification for the algebraic system relative to the normal system

lift-arr : {a b u v : D.ty} → N.coe-arr (a , b) (u , v) → N.coe-arr (D.f a , D.f b) (D.f u , D.f v)
lift-arr (N.ca-arr c d) = N.ca-arr (N.c-mono c) (N.c-mono d)
lift-arr (N.ca-fmap c) = N.ca-fmap (lift-arr c)

-----------
-- reify --
-----------
reify : {a b : A.ty} → A.coe a b → N.coe (reify-ty a) (reify-ty b)
reify-F : {a b : A.ty-F} → A.coe-F a b → N.coe (reify-ty-F a) (reify-ty-F b)
reify-noF : {a b : A.ty-noF} → A.coe-noF a b → N.coe (reify-ty-noF a) (reify-ty-noF b)
reify-arr : {a b : A.ty-arr} → A.coe-arr a b → N.coe-arr (reify-ty-arr a) (reify-ty-arr b)
reify (A.c-ty-F c) = reify-F c
reify (A.c-ty-noF c) = reify-noF c
reify-F (A.c-F-mono c) = N.c-mono (reify-F c)
reify-F (A.c-F-noF c) = N.c-mono (reify-noF c)
reify-noF A.c-noF-id = N.c-id
reify-noF (A.c-noF-arr c) = N.c-arr (reify-arr c)
reify-arr (A.c-arr-fmap-l c) = N.ca-fmap (reify-arr c)
reify-arr (A.c-arr-fmap-r c) = N.ca-fmap (reify-arr c)
reify-arr (A.c-arr-fmap-arr c) = N.ca-fmap (reify-arr c)
reify-arr (A.c-arr-mono c) =  lift-arr (reify-arr c)
reify-arr (A.c-arr-l c d) = N.ca-arr (reify-F c) (reify-noF d)
reify-arr (A.c-arr-r c d) = N.ca-arr (reify-noF c) (reify-F d)
reify-arr (A.c-arr-arr c d) =  N.ca-arr (reify-noF c) (reify-noF d)

mk-F : {a b : D.ty} →
  A.coe (eval-ty a) (eval-ty b) →
  A.coe-F (eval-ty-F a) (eval-ty-F b)
mk-F {D.base} {D.base} (A.c-ty-noF c) = A.c-F-noF c
mk-F {D.base} {b D.⇒ b₁} (A.c-ty-noF c) = A.c-F-noF c
mk-F {D.f a} {D.f b} (A.c-ty-F c) = A.c-F-mono c
mk-F {a D.⇒ a₁} {D.base} (A.c-ty-noF c) = A.c-F-noF c
mk-F {a D.⇒ a₁} {b D.⇒ b₁} (A.c-ty-noF c) = A.c-F-noF c

mk-arr-lift : {a b u v : D.ty} →
  A.coe-F (eval-ty-F u) (eval-ty-F a) →
  A.coe-F (eval-ty-F b) (eval-ty-F v) →
  A.coe-arr (A.ty-arr-lift (eval-ty-arr a b)) (A.ty-arr-lift (eval-ty-arr u v))
mk-arr-lift {D.base} {D.f b} {D.base} {D.f v} (A.c-F-noF c) (A.c-F-mono d) = A.c-arr-mono (A.c-arr-r c d)

mk-arr-lift {D.base} {D.base} {D.base} {D.base} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {D.base} {D.base} {D.base} {v D.⇒ v₁} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {D.base} {b D.⇒ b₁} {D.base} {D.base} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {D.base} {b D.⇒ b₁} {D.base} {v D.⇒ v₁} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)

mk-arr-lift {a D.⇒ a₁} {D.base} {D.base} {D.base} (A.c-F-noF c) d = A.c-arr-mono (A.c-arr-arr c A.c-noF-id)
mk-arr-lift {a D.⇒ a₁} {D.f b} {D.base} {D.base} (A.c-F-noF c) ()
mk-arr-lift {a D.⇒ a₁} {b D.⇒ b₁} {D.base} {D.base} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {a D.⇒ a₁} {D.base} {D.base} {D.f v} (A.c-F-noF c) ()
mk-arr-lift {a D.⇒ a₁} {D.f b} {D.base} {D.f v} (A.c-F-noF c) (A.c-F-mono d) = A.c-arr-mono (A.c-arr-r c d)
mk-arr-lift {a D.⇒ a₁} {D.base D.⇒ b₁} {D.base} {D.f v} (A.c-F-noF c) ()
mk-arr-lift {a D.⇒ a₁} {D.f b D.⇒ b₁} {D.base} {D.f v} (A.c-F-noF c) ()
mk-arr-lift {a D.⇒ a₁} {(b D.⇒ b₂) D.⇒ b₁} {D.base} {D.f v} (A.c-F-noF c) ()
mk-arr-lift {a D.⇒ a₁} {D.base} {D.base} {v D.⇒ v₁} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {a D.⇒ a₁} {D.f b} {D.base} {v D.⇒ v₁} (A.c-F-noF c) ()
mk-arr-lift {a D.⇒ a₁} {b D.⇒ b₁} {D.base} {v D.⇒ v₁} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {D.f a} {D.base} {D.f u} {D.base} (A.c-F-mono c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-l c d)
mk-arr-lift {D.f a} {D.base} {D.f u} {v D.⇒ v₁} (A.c-F-mono c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-l c d)
mk-arr-lift {D.f a} {D.f b} {D.f u} {D.f v} (A.c-F-mono c) (A.c-F-mono d) = A.c-arr-mono (mk-arr-lift c d)
mk-arr-lift {D.f a} {b D.⇒ b₁} {D.f u} {D.base} (A.c-F-mono c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-l c d)
mk-arr-lift {D.f a} {b D.⇒ b₁} {D.f u} {v D.⇒ v₁} (A.c-F-mono c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-l c d)
mk-arr-lift {D.base} {D.base} {u D.⇒ u₁} {D.base} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {D.base} {D.base} {u D.⇒ u₁} {D.f v} (A.c-F-noF c) ()
mk-arr-lift {D.base} {D.base} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {D.base} {D.f b} {u D.⇒ u₁} {D.base} (A.c-F-noF c) ()
mk-arr-lift {D.base} {D.f b} {u D.⇒ u₁} {D.f v} (A.c-F-noF c) (A.c-F-mono d) = A.c-arr-mono (A.c-arr-r c d)
mk-arr-lift {D.base} {D.f b} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-F-noF c) ()
mk-arr-lift {D.base} {b D.⇒ b₁} {u D.⇒ u₁} {D.base} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {D.base} {b D.⇒ b₁} {u D.⇒ u₁} {D.f v} (A.c-F-noF c) ()
mk-arr-lift {D.base} {b D.⇒ b₁} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {a D.⇒ a₁} {D.base} {u D.⇒ u₁} {D.base} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {a D.⇒ a₁} {D.base} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {a D.⇒ a₁} {D.f b} {u D.⇒ u₁} {D.base} (A.c-F-noF c) ()
mk-arr-lift {a D.⇒ a₁} {D.f b} {u D.⇒ u₁} {D.f v} (A.c-F-noF c) (A.c-F-mono d) = A.c-arr-mono (A.c-arr-r c d)
mk-arr-lift {a D.⇒ a₁} {D.f b} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-F-noF c) ()
mk-arr-lift {a D.⇒ a₁} {b D.⇒ b₁} {u D.⇒ u₁} {D.base} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)
mk-arr-lift {a D.⇒ a₁} {b D.⇒ b₁} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-F-noF c) (A.c-F-noF d) = A.c-arr-mono (A.c-arr-arr c d)

mk-arr : {a b u v : D.ty} →
  A.coe (eval-ty u) (eval-ty a) →
  A.coe (eval-ty b) (eval-ty v) →
  A.coe-arr (eval-ty-arr a b) (eval-ty-arr u v)

mk-arr {D.base} {D.base} {D.base} {D.base} c d = A.c-arr-arr A.c-noF-id A.c-noF-id
mk-arr {D.base} {D.base} {D.base} {v D.⇒ v₁} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {D.base} {D.base} {u D.⇒ u₁} {D.base} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {D.base} {D.base} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {D.base} {D.f b} {D.base} {D.f v} (A.c-ty-noF c) (A.c-ty-F c₁) = A.c-arr-r c c₁
mk-arr {D.base} {D.f b} {u D.⇒ u₁} {D.f v} (A.c-ty-noF c) (A.c-ty-F c₁) = A.c-arr-r c c₁
mk-arr {D.base} {b D.⇒ b₁} {D.base} {D.base} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {D.base} {b D.⇒ b₁} {D.base} {v D.⇒ v₁} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {D.base} {b D.⇒ b₁} {u D.⇒ u₁} {D.base} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {D.base} {b D.⇒ b₁} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {D.f a} {D.base} {D.f u} {D.base} (A.c-ty-F c) (A.c-ty-noF c₁) = A.c-arr-l c c₁
mk-arr {D.f a} {D.base} {D.f u} {v D.⇒ v₁} (A.c-ty-F c) (A.c-ty-noF c₁) = A.c-arr-l c c₁
mk-arr {D.f a} {D.f b} {D.f u} {D.f v} (A.c-ty-F c) (A.c-ty-F d) = mk-arr-lift c d
mk-arr {D.f a} {b D.⇒ b₁} {D.f u} {D.base} (A.c-ty-F c) (A.c-ty-noF c₁) = A.c-arr-l c c₁
mk-arr {D.f a} {b D.⇒ b₁} {D.f u} {v D.⇒ v₁} (A.c-ty-F c) (A.c-ty-noF c₁) = A.c-arr-l c c₁
mk-arr {a D.⇒ a₁} {D.base} {D.base} {D.base} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {a D.⇒ a₁} {D.base} {D.base} {v D.⇒ v₁} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {a D.⇒ a₁} {D.base} {u D.⇒ u₁} {D.base} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {a D.⇒ a₁} {D.base} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {a D.⇒ a₁} {D.f b} {D.base} {D.f v} (A.c-ty-noF c) (A.c-ty-F c₁) = A.c-arr-r c c₁
mk-arr {a D.⇒ a₁} {D.f b} {u D.⇒ u₁} {D.f v} (A.c-ty-noF c) (A.c-ty-F c₁) = A.c-arr-r c c₁
mk-arr {a D.⇒ a₁} {b D.⇒ b₁} {D.base} {D.base} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {a D.⇒ a₁} {b D.⇒ b₁} {D.base} {v D.⇒ v₁} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {a D.⇒ a₁} {b D.⇒ b₁} {u D.⇒ u₁} {D.base} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁
mk-arr {a D.⇒ a₁} {b D.⇒ b₁} {u D.⇒ u₁} {v D.⇒ v₁} (A.c-ty-noF c) (A.c-ty-noF c₁) = A.c-arr-arr c c₁

mk-fmap : {a b : D.ty} {u : A.ty-arr} →
  A.coe-arr (eval-ty-arr a b) u →
  A.coe-arr (eval-ty-arr a b) (A.ty-arr-lift u)
mk-fmap {D.base} {D.base} {u} c = A.c-arr-fmap-arr c
mk-fmap {D.base} {D.f b} {u} (A.c-arr-fmap-r c) = A.c-arr-fmap-r (A.c-arr-fmap-r c)
mk-fmap {D.base} {D.f b} {u} (A.c-arr-r x x₁) = A.c-arr-fmap-r (A.c-arr-r x x₁)
mk-fmap {D.base} {b D.⇒ b₁} {u} (A.c-arr-fmap-arr c) = A.c-arr-fmap-arr (A.c-arr-fmap-arr c)
mk-fmap {D.base} {b D.⇒ b₁} {u} (A.c-arr-arr x x₁) = A.c-arr-fmap-arr (A.c-arr-arr x x₁)
mk-fmap {D.f a} {D.base} {u} (A.c-arr-fmap-l c) = A.c-arr-fmap-l (A.c-arr-fmap-l c)
mk-fmap {D.f a} {D.base} {u} (A.c-arr-l x x₁) = A.c-arr-fmap-l (A.c-arr-l x x₁)
mk-fmap {D.f a} {D.f b} {u} (A.c-arr-mono c) = A.c-arr-mono (mk-fmap c)
mk-fmap {D.f a} {b D.⇒ b₁} {u} (A.c-arr-fmap-l c) = A.c-arr-fmap-l (A.c-arr-fmap-l c)
mk-fmap {D.f a} {b D.⇒ b₁} {u} (A.c-arr-l x x₁) = A.c-arr-fmap-l (A.c-arr-l x x₁)
mk-fmap {a D.⇒ a₁} {D.base} {u} (A.c-arr-fmap-arr c) = A.c-arr-fmap-arr (A.c-arr-fmap-arr c)
mk-fmap {a D.⇒ a₁} {D.base} {u} (A.c-arr-arr x x₁) = A.c-arr-fmap-arr (A.c-arr-arr x x₁)
mk-fmap {a D.⇒ a₁} {D.f b} {u} (A.c-arr-fmap-r c) = A.c-arr-fmap-r (A.c-arr-fmap-r c)
mk-fmap {a D.⇒ a₁} {D.f b} {u} (A.c-arr-r x x₁) = A.c-arr-fmap-r (A.c-arr-r x x₁)
mk-fmap {a D.⇒ a₁} {b D.⇒ b₁} {u} c = A.c-arr-fmap-arr c

eval : {a b : D.ty} → N.coe a b → A.coe (eval-ty a) (eval-ty b)
eval-F : {a b : D.ty} → N.coe a b → A.coe-F (eval-ty-F a) (eval-ty-F b)
eval-arr : {a b u v : D.ty} →
  N.coe-arr (a , b) (u , v) →
  A.coe-arr (eval-ty-arr a b) (eval-ty-arr u v)
eval N.c-id = A.c-ty-noF A.c-noF-id
eval (N.c-mono c) = A.c-ty-F (eval-F c)
eval (N.c-arr c) = A.c-ty-noF (A.c-noF-arr (eval-arr c))
eval-arr (N.ca-arr c d) =  mk-arr (eval c) (eval d)
eval-arr (N.ca-fmap c) = mk-fmap (eval-arr c)
eval-F c = mk-F (eval c)
