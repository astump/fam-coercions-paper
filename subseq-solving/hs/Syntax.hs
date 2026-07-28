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

subSeqSetWith :: [Const] -> [Const] -> Var -> Bool -> Constraint
subSeqSetWith l1 l2 lk True = Subseq (Const <$> l1) (Var lk : (Const <$> l2))
-- subSeqSetWith l1 l2 lk False = Subseq (lk ++ l1) l2

-- compute constraint for the root node of the tree
getConstraint :: SubtypeTree -> Constraint
getConstraint (NatSubtype l1 lk b l2) = subSeqSetWith l1 l2 lk b

subtype :: Var -> Bool -> Tp -> Tp -> SubtypeTree
subtype = undefined