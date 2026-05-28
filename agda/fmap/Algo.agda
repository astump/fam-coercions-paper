module fmap.Algo where

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
