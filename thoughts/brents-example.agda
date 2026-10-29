Brent's example of incoherent coercions:

1. pure : F B <: F (F B)

2. fmap pure : F B <: F (F B)

These are computationally different:

pure Nothing = Just Nothing

fmap pure Nothing = Nothing

----------------------------------------------------------------------
This seems to depend on nested uses of the same functor.

Because:

1. this is not type-correct: pure : F B <: F (G B)

2. but this is fine: fmap pure : F B <: F (G B)

Similarly

1. this is fine: pure : F B <: G (F B)

2. but this is not: fmap pure : F B <: G (F B)

----------------------------------------------------------------------
Caden observes:

The problem is actually similar to the head :: [a] -> a, xs :: [[a]] example,
because here it is pure that is polymorphic and can be used in two different:

1. pure : B -> F B
2. pure : F B -> F (F B)

So the head example is like the dual of Brent's example:

1. head xs :: [ a ]
2. fmap head xs :: [ a ]

head :: [a] -> a

is like

copure :: F A -> A

and we have

1. copure      : F (F A) <: F A
2. fmap copure : F (F A) <: F A

And maybe these are different?