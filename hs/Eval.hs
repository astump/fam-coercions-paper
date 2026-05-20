module Eval where

data Expr = Fail | Int Int | Add Expr Expr

eval :: Expr -> Maybe Int
eval Fail = Nothing
eval (Int x) = Just x
eval (Add e1 e2) =
  do
    r1 <- eval e1
    r2 <- eval e2
    return $ r1 + r2

{- futuristic version with coercive subtyping for monads

eval :: Expr -> Maybe Int
eval Fail = Nothing
eval (Int x) = x
eval (Add e1 e2) = eval e1 + eval e2

-}