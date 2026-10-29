1 ≤ 1          0 ≤ -1 + 2 
-----------   ----------------
F A < 1 ] A    B < -1 ] F (F B)
-------------------------------  (j = 1)
F (A ⇒ B) < 0 ] F A ⇒ F (F B)

n = 1
m = 0
k = 0
        j ≥ 1


F (A ⇒ B) <: [ap]
F A ⇒ F B <: [arrow id pure]
F A ⇒ F (F B)

With f : F (A ⇒ B)
get

pure ∘ ap f ∘ id : F A ⇒ F (F B)

which is just

pure ∘ ap f : F A ⇒ F (F B)
======================================================================

1 ≤ 2          0 ≤ -2 + 2 
-----------   ----------------
F A < 2 ] A    B < -2 ] F (F B)
-------------------------------  (j = 2)
F (A ⇒ B) < 0 ] F A ⇒ F (F B)

n = 1
m = 0
k = 0

F (A ⇒ B)         <: [ap]
F A ⇒ F B         <: [pure]
F (F A ⇒ F B)     <: [ap]
F (F A) ⇒ F (F B) <: [arrow pure id]
F A ⇒ F (F B)

With f : F (A ⇒ B)
get

id ∘ ap (pure (ap f)) ∘ pure : F A ⇒ F F B

which equals 

ap (pure (ap f)) ∘ pure : F A ⇒ F F B

----------------------------------------------------------------------
Have f : F (A ⇒ B).

Finally, the two results of coercion, of type F A ⇒ F (F B), are

c1 = pure ∘ ap f 

c2 = ap (pure (ap f)) ∘ pure

But these are equivalent:

  c1 x
= (pure ∘ ap f) x
= pure (ap f x)

  c2 x
= (ap (pure (ap f)) ∘ pure) x
= (ap (pure (ap f))) (pure x)
= (fmap (ap f)) (pure x)
= (pure (ap f x))
