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

mk-f : A.ty → A.ty
mk-f (A.ty-ty-F t) = A.ty-ty-F (A.ty-F-F t)
mk-f (A.ty-ty-noF t) = A.ty-ty-F (A.ty-F-noF t)

repr-mk-f : ∀ {a u} →
  repr-ty a u →
  repr-ty (mk-f a) (D.f u)
repr-mk-f (repr-ty-ty-F r) = repr-ty-ty-F (repr-ty-F-F r)
repr-mk-f (repr-ty-ty-noF r) = repr-ty-ty-F (repr-ty-F-noF r)

repr-ty-arr-inv-l : ∀ {uv} {u} {v} →
  repr-ty-arr uv u v →
  Σ[ u' ∈ A.ty ] repr-ty u' u
repr-ty-arr-inv-l (repr-ty-arr-lift r-arr) =
  let (u' , urep) = (repr-ty-arr-inv-l r-arr) in
  mk-f u' , repr-mk-f urep
repr-ty-arr-inv-l (repr-ty-arr-l ru rv) = A.ty-ty-F _ , repr-ty-ty-F ru
repr-ty-arr-inv-l (repr-ty-arr-r ru rv) = A.ty-ty-noF _ , repr-ty-ty-noF ru
repr-ty-arr-inv-l (repr-ty-arr-arr ru rv) = A.ty-ty-noF _ , repr-ty-ty-noF ru

repr-ty-arr-inv-r : ∀ {uv} {u} {v} →
  repr-ty-arr uv u v →
  Σ[ v' ∈ A.ty ] repr-ty v' v
repr-ty-arr-inv-r (repr-ty-arr-lift r-arr) =
  let (v' , vrep) = (repr-ty-arr-inv-r r-arr) in
  mk-f v' , repr-mk-f vrep
repr-ty-arr-inv-r (repr-ty-arr-l ru rv) = A.ty-ty-noF _ , repr-ty-ty-noF rv
repr-ty-arr-inv-r (repr-ty-arr-r ru rv) = A.ty-ty-F _ , repr-ty-ty-F rv
repr-ty-arr-inv-r (repr-ty-arr-arr ru rv) = A.ty-ty-noF _ , repr-ty-ty-noF rv

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

mk-arr : ∀ {a b u v} {a' b' u' v'} {ab uv} →
  repr-ty-arr ab a b →
  repr-ty-arr uv u v →
  repr-ty a' a →
  repr-ty b' b →
  repr-ty u' u →
  repr-ty v' v →
  A.coe u' a' →
  A.coe b' v' →
  A.coe-arr ab uv
mk-arr-F-F : ∀ {a b u v} {a' b' u' v'} {ab uv} →
  repr-ty-arr ab a b →
  repr-ty-arr uv u v →
  repr-ty-F a' a →
  repr-ty-F b' b →
  repr-ty-F u' u →
  repr-ty-F v' v →
  A.coe-F u' a' →
  A.coe-F b' v' →
  A.coe-arr ab uv
mk-arr-noF-noF : ∀ {a b u v} {a' b' u' v'} {ab uv} →
  repr-ty-arr ab a b →
  repr-ty-arr uv u v →
  repr-ty-noF a' a →
  repr-ty-noF b' b →
  repr-ty-noF u' u →
  repr-ty-noF v' v →
  A.coe-noF u' a' →
  A.coe-noF b' v' →
  A.coe-arr ab uv
mk-arr-F-noF : ∀ {a b u v} {a' b' u' v'} {ab uv} →
  repr-ty-arr ab (D.f a) b →
  repr-ty-arr uv (D.f u) v →
  repr-ty-F a' a →
  repr-ty-noF b' b →
  repr-ty-F u' u →
  repr-ty-noF v' v →
  A.coe-F u' a' →
  A.coe-noF b' v' →
  A.coe-arr ab uv
mk-arr-noF-F : ∀ {a b u v} {a' b' u' v'} {ab uv} →
  repr-ty-arr ab a (D.f b) →
  repr-ty-arr uv u (D.f v) →
  repr-ty-noF a' a →
  repr-ty-F b' b →
  repr-ty-noF u' u →
  repr-ty-F v' v →
  A.coe-noF u' a' →
  A.coe-F b' v' →
  A.coe-arr ab uv
mk-arr-F-F (repr-ty-arr-lift r-ab) (repr-ty-arr-lift r-uv) (repr-ty-F-F r-a) (repr-ty-F-F r-b) (repr-ty-F-F r-u) (repr-ty-F-F r-v) (A.c-F-mono c) (A.c-F-mono d) = {!!}
mk-arr-F-F (repr-ty-arr-lift r-ab) (repr-ty-arr-l r-uv) (repr-ty-F-F r-a) (repr-ty-F-F r-b) (repr-ty-F-F r-u) (repr-ty-F-F r-v) (A.c-F-mono c) (A.c-F-mono d) = {!!}
mk-arr-F-F r-ab r-uv r-a r-b r-u r-v (A.c-F-mono c) (A.c-F-noF d) = {!!}
mk-arr-F-F r-ab r-uv r-a r-b r-u r-v (A.c-F-noF c) (A.c-F-mono d) = {!!}
mk-arr-F-F r-ab r-uv r-a r-b r-u r-v (A.c-F-noF c) (A.c-F-noF d) = {!!}
mk-arr-noF-noF r-ab r-uv r-a r-b r-u r-v c d = {!!}
mk-arr-F-noF r-ab r-uv r-a r-b r-u r-v c d = {!!}
mk-arr-noF-F r-ab r-uv r-a r-b r-u r-v c d = {!!}
mk-arr (repr-ty-arr-lift r-ab) (repr-ty-arr-lift r-uv)
  (repr-ty-ty-F r-a)
  (repr-ty-ty-F r-b)
  (repr-ty-ty-F r-u)
  (repr-ty-ty-F r-v)
  (A.c-ty-F c) (A.c-ty-F d) = A.c-arr-mono (mk-arr-F-F r-ab r-uv r-a r-b r-u r-v c d)
mk-arr r-ab r-uv (repr-ty-ty-F r-a) (repr-ty-ty-noF r-b) (repr-ty-ty-F r-u) (repr-ty-ty-noF r-v)
  (A.c-ty-F c) (A.c-ty-noF d) = mk-arr-F-noF r-ab r-uv r-a r-b r-u r-v c d
mk-arr r-ab r-uv (repr-ty-ty-noF r-a) (repr-ty-ty-F r-b) (repr-ty-ty-noF r-u) (repr-ty-ty-F r-v)
  (A.c-ty-noF c) (A.c-ty-F d) = mk-arr-noF-F r-ab r-uv r-a r-b r-u r-v c d
mk-arr r-ab r-uv (repr-ty-ty-noF r-a)
                 (repr-ty-ty-noF r-b)
                 (repr-ty-ty-noF r-u)
                 (repr-ty-ty-noF r-v)
                 (A.c-ty-noF c)
                 (A.c-ty-noF d) = mk-arr-noF-noF r-ab r-uv r-a r-b r-u r-v c d

mk-F : {a b : D.ty} →
  A.coe (eval-ty a) (eval-ty b) →
  A.coe-F (eval-ty-F a) (eval-ty-F b)
mk-F {D.base} {D.base} (A.c-ty-noF c) = A.c-F-noF c
mk-F {D.base} {b D.⇒ b₁} (A.c-ty-noF c) = A.c-F-noF c
mk-F {D.f a} {D.f b} (A.c-ty-F c) = A.c-F-mono c
mk-F {a D.⇒ a₁} {D.base} (A.c-ty-noF c) = A.c-F-noF c
mk-F {a D.⇒ a₁} {b D.⇒ b₁} (A.c-ty-noF c) = A.c-F-noF c


eval : {a b : D.ty} {a' b' : A.ty} →
  repr-ty a' a →
  repr-ty b' b →
  N.coe a b →
  A.coe a' b'
eval-F : {a b : D.ty} {a' b' : A.ty-F} →
  repr-ty-F a' a →
  repr-ty-F b' b →
  N.coe a b →
  A.coe-F a' b'
eval-arr : {a b u v : D.ty} {ab uv : A.ty-arr} →
  repr-ty-arr ab a b →
  repr-ty-arr uv u v →
  N.coe-arr (a , b) (u , v) →
  A.coe-arr ab uv
eval (repr-ty-ty-noF repr-ty-noF-bool)
     (repr-ty-ty-noF repr-ty-noF-bool)
     N.c-id =
     A.c-ty-noF A.c-noF-id
eval (repr-ty-ty-F r-a)
     (repr-ty-ty-F r-b)
     (N.c-mono c) =
     A.c-ty-F (eval-F r-a r-b c)
eval (repr-ty-ty-noF (repr-ty-noF-arr r-a))
     (repr-ty-ty-noF (repr-ty-noF-arr r-b))
     (N.c-arr c) =
     A.c-ty-noF (A.c-noF-arr (eval-arr r-a r-b c))

eval-F (repr-ty-F-noF repr-ty-noF-bool) (repr-ty-F-noF repr-ty-noF-bool) N.c-id = A.c-F-noF A.c-noF-id
eval-F (repr-ty-F-F r-a) (repr-ty-F-F r-b) (N.c-mono c) = A.c-F-mono (eval-F r-a r-b c)
eval-F (repr-ty-F-noF (repr-ty-noF-arr r-a)) (repr-ty-F-noF (repr-ty-noF-arr r-b)) (N.c-arr c) =
  A.c-F-noF (A.c-noF-arr (eval-arr r-a r-b c))
eval-arr r-ab r-uv (N.ca-arr c d) =
  let a' , r-a' = repr-ty-arr-inv-l r-ab in
  let b' , r-b' = repr-ty-arr-inv-r r-ab in
  let u' , r-u' = repr-ty-arr-inv-l r-uv in
  let v' , r-v' = repr-ty-arr-inv-r r-uv in
  let x = eval r-u' r-a' c in
  let y = eval r-b' r-v' d in
  {!!}
  --{!mk-arr ? ? !}

eval-arr (repr-ty-arr-lift r-ab) (repr-ty-arr-lift r-uv) (N.ca-fmap c') = {!!}
eval-arr (repr-ty-arr-l c d) (repr-ty-arr-lift r-uv) (N.ca-fmap c') = A.c-arr-fmap-l (eval-arr (repr-ty-arr-l c d) r-uv c')
eval-arr (repr-ty-arr-r c d) (repr-ty-arr-lift r-uv) (N.ca-fmap c') = A.c-arr-fmap-r (eval-arr (repr-ty-arr-r c d) r-uv c')
eval-arr (repr-ty-arr-arr c d) (repr-ty-arr-lift r-uv) (N.ca-fmap c') = A.c-arr-fmap-arr (eval-arr (repr-ty-arr-arr c d) r-uv c')
