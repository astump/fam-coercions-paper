All pairs of distinct coercions with the same type, to depth 4, are reducible
through rewriting to one of the following cases, or some combination of them
(verified by brute-force enumeration):

1. fmap pure : F X <: F (F X)
   pure : F X <: F (F X)

2. pure . fun (pure . c1) c2 . ap : F (X -> Y) <: F (W -> Z)
   fmap (fun c1 (c2 . pure)) : F (X -> Y) <: F (W -> Z)
   for any c1 : W <: X and c2 : F Y <: Z

3. fun (fun pure id . ap) (pure . c) : ((X -> F Y) -> Z) <: (F (X -> Y) -> F W)
   ap . pure . fun (fun id pure) c : ((X -> F Y) -> Z) <: (F (X -> Y) -> F W)
   for any c : Z <: W.

For cases 1 and 2, it is trivial to see that the coercions are computationally
different. If l is a list then fmap f l always has the same length as l, while
pure l always has length 1. 

In case 2, if we have c2 = fmap c3, then this becomes the pair:

pure . fun (pure . c1) (fmap c3) . ap : F (X -> Y) <: F (W -> F Z)
fmap (fun c1 (fmap c3 . pure)) : F (X -> Y) <: F (W -> F Z)

which is equivalent to:

pure . fun (pure . c1) (fmap c3) . ap  : F (X -> Y) <: F (W -> F Z)
fmap (fun c1 (pure . c3)) : F (X -> Y) <: F (W -> F Z)

The coercions in this pair have the same number of fmaps, although the first additionally has an ap.

Note also that if we did not apply this last rewrite step, then the first
coercion has 1 fmap and 1 ap, while the second has 2 fmaps.
----------------------------------------------------------------------
Case 3 is less obvious, but can be seen by evaluating on an
example. It may be possible to reduce case 3 to cases 1 and 2,
although I have been unable to do so.

Here is a walk through the coercions, using a notation where the coercion
itself is written following the subtyping symbol, for each step in a
composition of coercions, and coercions for fun are written underneath
with dashes.

The first coercion is fun (fun pure id . ap) (pure . c):

((X -> F Y) -> Z)   <: [fun]
(F (X -> Y) -> F W)    by
  - F (X -> Y) <: [ap]
    F X -> F Y <: [fun] 
    X -> F Y      by
    - X <:   [pure]
      F X
    - F Y <: [id]
      F Y
  - Z  <: [c]
    W  <: [pure]
    F W

The second coercion is ap . pure . fun (fun id pure) c:

(X -> F Y) -> Z <: [fun]
(X -> Y)   -> W 
 - (X -> Y)   <: [fun]
   (X -> F Y)    by
   - X <: [id]
     X
   - Y <: [pure]
     F Y
 - Z <: [c]
   W
<: [pure]
F ((X -> Y) -> W)   <: [ap]
F (X -> Y)  -> F W



----------------------------------------------------------------------
The search space for depth 5 is much too large for the same brute-force approach.
