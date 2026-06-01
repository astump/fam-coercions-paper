module fmap.Algo where

-----------
-- types --
-----------
data ty : Set
data ty-noF : Set
data ty-F : Set
data ty-arr : Set
data ty where
  ty-ty-F : ty-F → ty
  ty-ty-noF : ty-noF → ty
data ty-F where
  ty-F-F : ty-F → ty-F
  ty-F-noF : ty-noF → ty-F -- this is meant to represent F t, not embed t into ty-F without tagging it
data ty-noF where
  nt-bool : ty-noF
  nt-arr : ty-arr → ty-noF
data ty-arr where
  ty-arr-lift : ty-arr → ty-arr
  ty-arr-l : ty-F → ty-noF → ty-arr
  ty-arr-r : ty-noF → ty-F → ty-arr
  ty-arr-arr : ty-noF → ty-noF → ty-arr

---------------
-- coercions --
---------------

data coe-F : ty-F → ty-F → Set
data coe : ty → ty → Set
data coe-noF : ty-noF → ty-noF → Set
data coe-arr : ty-arr → ty-arr → Set

data coe where
  c-ty-F : {a b : ty-F} → coe-F a b → coe (ty-ty-F a) (ty-ty-F b)
  c-ty-noF : {a b : ty-noF} → coe-noF a b → coe (ty-ty-noF a) (ty-ty-noF b)

data coe-F where
  c-F-mono : {a b : ty-F} →
    coe-F a b →
    coe-F (ty-F-F a) (ty-F-F b)
  c-F-noF : {a b : ty-noF} →
    coe-noF a b →
    coe-F (ty-F-noF a) (ty-F-noF b)

data coe-noF where
  c-noF-id : coe-noF nt-bool nt-bool
  c-noF-arr : {a b : ty-arr} →
    coe-arr a b →
    coe-noF (nt-arr a) (nt-arr b)

-- a b <= ffa ffb
-- get this by going
data coe-arr where
  c-arr-fmap-l : {a : ty-F} {b : ty-noF} {u : ty-arr} →
    coe-arr (ty-arr-l a b) u →
    coe-arr (ty-arr-l a b) (ty-arr-lift u)
  c-arr-fmap-r : {a : ty-noF} {b : ty-F} {u : ty-arr} →
    coe-arr (ty-arr-r a b) u →
    coe-arr (ty-arr-r a b) (ty-arr-lift u)
  c-arr-fmap-arr : {a b : ty-noF} {u : ty-arr} →
    coe-arr (ty-arr-arr a b) u →
    coe-arr (ty-arr-arr a b) (ty-arr-lift u)
  c-arr-mono : {a b : ty-arr} →
    coe-arr a b →
    coe-arr (ty-arr-lift a) (ty-arr-lift b)
  c-arr-l : {a u : ty-F} {b v : ty-noF} →
    coe-F u a →
    coe-noF b v →
    coe-arr (ty-arr-l a b) (ty-arr-l u v)
  c-arr-r : {a u : ty-noF} {b v : ty-F} →
    coe-noF u a →
    coe-F b v →
    coe-arr (ty-arr-r a b) (ty-arr-r u v)
  c-arr-arr : {a u b v : ty-noF} →
    coe-noF u a →
    coe-noF b v →
    coe-arr (ty-arr-arr a b) (ty-arr-arr u v)
