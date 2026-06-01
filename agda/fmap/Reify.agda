module fmap.Reify where
open import Relation.Binary.PropositionalEquality
open import Data.Product
import fmap.Algo as A
import fmap.Decl as D
import fmap.Normal as N
open import fmap.TypeIso

-- reification for the algebraic system relative to the normal system

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
reify-arr c = {!!}

eval : {a b : D.ty} → N.coe a b → A.coe (eval-ty a) (eval-ty b)
eval-F : {a b : D.ty} → N.coe a b → A.coe-F (eval-ty-F a) (eval-ty-F b)
eval-arr : {a b u v : D.ty} →
  N.coe-arr (a , b) (u , v) →
  A.coe-arr (eval-ty-arr a b) (eval-ty-arr u v)
eval N.c-id = A.c-ty-noF A.c-noF-id
eval (N.c-mono c) = A.c-ty-F (eval-F c)
eval (N.c-arr c) = A.c-ty-noF (A.c-noF-arr (eval-arr c))
eval-arr {D.f a} {D.f b} {D.f u} {D.f v} (N.ca-arr c d) = {!!}
eval-arr {a} {b} {u} {v} (N.ca-arr c d) = {!!}
eval-arr (N.ca-fmap c) = {!!}
eval-F c = {!!}
