# Notes from post-HASKELL 2026 deadline

I like this paper. Writing the workshop (symposium?) paper gave me some clearer
ideas about where the problems are and what we ought to do next.

## Ideas and problems 

In a declarative system with a subsumption rule, if you have `e : A` then for
every subtyping `A <: B` you also get `c(e) : B` for some coercion `c`. These
terms may not be equivalent. The coherence claim only has to say that if `|-
e ~~> e' : B` and `|- e ~~> e'' : B` then `e' ~= e''`. We only care about
derivations that assign the same type.

To keep this from producing incoherence in practice, we also need to prove that
type inference always produces a principal type for a term and those types are
unique. That tells you that if `|- e ~~> e' : A` and `|- e ~~> e'' : B`,
then `A = B`, so `e' ~= e''`. It also tells you that if you come up with some
other type `C` for `e` in the declarative system, it's less general (more
monomorphic, more lifted/fmapped/etc) than `A`.

The easiest way to prove this kind of result is by appealing to an untyped
semantics where subtyping can be interpreted by something like refinement or
simulation. If A <: B, then values in [[A]] are also values in [[B]].
A call-by-value logical relation model might work, with the values of type A ->
B defined to be lambdas that turn As into Bs under some number of fmaps.

```
  V[[A -> B]] = { \x. e | exists k. forall a. fmap^k (\x. e) a in C[[B]] }.

  C[[A]] = { e | forall v. if e -->* v then v in V[[A]] }
```

Unfortunately, for functors with polymorphism, coherence as stated is not
true, since there are typings like
  head [[1,2],[3,4]] : List Int
which come with two possible elaborations which are not equal. The working
hypothesis here is that the "bad" elaboration, which inserts a coercion instead
of instantiating a quantifier, can somehow be ruled out.

There may be a system of subtypings including explicit "instantiation" coercions
  T[alpha] ----> T[U].
Those instantiations ought to commute with uses of fmap and the like, so you
could factor them into (1) instantiations [theta] followed by (2) "true
coercions" [c]. This might make it possible to put a ranking on them, but
I haven't been able to get it to work yet. If there is a ranking, then we might
be able to recover coherence by requiring inference to always pick the coercion
with the lowest rank.

In this vein of worjk:
> Coherence for Qualified Types
> Mark P. Jones
> https://www.cs.yale.edu/publications/techreports/tr989.pdf

This is a short tech report. I think his dissertation covers the same stuff at
greater length.

> Qualified Types: Theory and Practice 
> Mark P. Jones
> https://www.cs.ox.ac.uk/files/3432/PRG106.pdf

In section 5.3 there is an example of an incoherent subtyping that gets
subsequently ruled out by "principal typing" conditions, which is similar to our
situation with functors and polymorphism. His work was motivated by Haskell
typeclass resolution issues, so it's not got an immediate solution, but the
shape of the results may be helpful.

### Tensions
We are going to have to choose, on some level, between a polymorphic system and
a complete system. It is significantly less work to design, implement, and
verify monomorphic systems. I do think a result for polymorphism would be
stronger evidence that the system is workable in practice and I want to try
to figure it out.

By the same token, extending to applicatives seems achievable while extending to
monads may be more difficult, especially when combined with polymorphism. The
situation for applicatives seems more worth it, comparatively, and every monad
is an applicative anyway.

Constraint solving using Chronolog may be difficult if our rules need to appeal
to (say) a weird unification algorithm that is not the same as the unification
algorithm in Chronolog.

## Things to do next or a prospective project outline
For a given typeclass, whether it's functors, applicatives, or monads, I think
we could do something like the following. If there's a way to do all of this for
everything, well, even better. I think the metatheory is probably pretty
modular, the implementations might also turn out to be modular since we mostly
use Chronolog to do the fiddly bits.

### Definitions

1. A declarative type system *D* that uses the declarative coercion judgment (on unannotated terms)
2. An algorithmic type system *A* that uses the algorithmic coercion judgment (on fully annotated terms)
3. A type inference and elaboration system *E* on unannotated terms that
   produces annotated terms (which type check under the algorithmic system).

### Theorems

1. Coherence of declarative coercions
2. Coherence for type inference: if elaborating e at type A produces e' or e'',
   then e' is equivalent to e'' under contextual equivalence (or some easier to
   handle overapproximation), up to $typeclass laws
3. Soundness of type inference: elaborated terms type check
4. Principality of type inference: when inference succeeds, the inferred types
   are more general than any other type that could be ascribed by the
   declarative system
5. Completeness of type inference: if an annotated term type checks and you
   erase types from the term, its type (or a more general one) can be
   re-inferred.

I think the proof of coherence for type inference is going to rely on the proof
of principal typing.

Proving things about type inference is hard. There is a 2024 paper

> Type Inference Logics
> Denis Carnier, François Pottier, and Steven Keuchel
> OOPSLA 2024
> https://dl.acm.org/doi/pdf/10.1145/3689786

which treats type inference algorithms as monadic programs whose effect is "name
generation" or "constraint generation." I think this is interesting and probably
the most economical route to verifying an algorithm in a proof assistant. They
do more than I would think to do, in that they also verify the solver itself
rather than just specifying its behavior. But I think this is important for
a completeness claim.

### Implementation

1. Syntax and parsing
   - Essentially the DCS frontend but maybe with some support for extra type
     annotations as needed for type inference to work
   - A form of declaration for introducing instances of Functor, Applicative,
     Monad, etc as newtypes
2. A frontend that implements *E* and produces elaborated syntax
3. A type checker for elaborated syntax that implements the algorithmic system.

### Evaluation

1. Test suite showing the thing works
   - Make sure elaborated output checks under the elaborated system
   - Find some way of showing that things don't get over-generalized or
     over-lifted? Maybe a kind of mutation testing would work for this, where
     you take a well-typed term and erase the types and show that the
     re-inferred type is at least as general as the original one.
2. Extended case studies

In this section of things I think we could really make up for lack of theorems
by thorough fuzzing. I like fuzzing and testing for type inference. The trouble
of course is that if it keeps finding bugs it gets harder and harder to fix
them. So it's really only a good idea if we are truly confident the algorithm
can work (in whatever sense).
