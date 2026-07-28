module Syntax where

import Prelude hiding (Word)

type Const = String

type Var = String

data Tp = Nat [Const] | Arrow [Const] Tp Tp

data Symbol = Const Const | Var Var

type Word = [Symbol]

data Constraint = Subseq Word Word

{- compare to NatRefl and Fun in ../../agda/multi-constructor/Decproc.agda -}
data SubtypeTree =
   NatSubtype [Const] {- l1 -} Var {- lk -} Bool {- b -} [Const] {- l2 -}
 | FunSubtype [Const] {- l1 -} Var {- lk -} Bool {- b -} [Const] {- l2 -} Var {- j -}

subSeqSetWith :: Word -> Word -> Var -> Bool -> Constraint
subSeqSetWith l1 l2 lk True = Subseq l1 (Var lk : l2)
-- subSeqSetWith l1 l2 lk False = Subseq (lk ++ l1) l2

-- compute constraint for the root node of the tree
getConstraint :: SubtypeTree -> Constraint
getConstraint (NatSubtype l1 lk b l2) = subSeqSetWith (Const <$> l1) (Const <$> l2) lk b
getConstraint (FunSubtype l1 lk b l2 j) = subSeqSetWith (Const <$> l1) ((Const <$> l2) ++ [Var j]) lk b

{- subtype k b T1 T2 is supposed to produce the SubtypeTree
   holding the same information we find in Decproc.agda's data structure with NatRefl and Fun.

   We will then process that tree recursively to compute all the possible solutions for the
   subtyping problem. -}
subtype :: Var -> Bool -> Tp -> Tp -> SubtypeTree
subtype = undefined