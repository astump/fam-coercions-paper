module DecprocExamples where

open import lib
open import Tp
open import ExtraIntegerLemmas
open import Declarative
open import Decproc
--open import Semantics

ex1 : 1 ! (0 !N) ⇒ (0 !N) < mkℤ 1 tt ] 0 ! 0 !N ⇒ 0 !N
ex1 = Fun{j = 0ℤ} refl refl (NatRefl refl) (NatRefl refl)

ex2 : 1 ! (0 !N) ⇒ (0 !N) < 0ℤ ] 0 ! 0 !N ⇒ 1 !N
ex2 = Fun{j = toℤ 1} refl refl (NatRefl refl) (NatRefl refl)

ex3 : 1 ! (0 !N) ⇒ (0 !N) < 0ℤ ] 1 ! 0 !N ⇒ 1 !N
ex3 = Fun{j = 0ℤ} refl refl (NatRefl refl) (NatRefl refl)

ex4 : 1 ! (0 !N) ⇒ (0 !N) < toℤ 1 ] 0 ! 0 !N ⇒ 1 !N
ex4 = Fun{j = toℤ 1} refl refl (NatRefl refl) (NatRefl refl)


--test : Set
--test = ⊨ 1 ! (0 ! (0 !N) ⇒ (2 !N)) ⇒ (0 !N)   < 0ℤ ]   0 ! (0 ! (1 !N) ⇒ (1 !N)) ⇒ (1 !N)

ex5 : 1 ! (0 ! (0 !N) ⇒ (2 !N)) ⇒ (0 !N)   < 0ℤ ]   0 ! (0 ! (1 !N) ⇒ (1 !N)) ⇒ (1 !N)
ex5 = Fun{j = toℤ 1} refl refl (Fun{j = toℤ 1}  refl refl (NatRefl refl) (NatRefl refl)) (NatRefl refl)

ex6 : 0 ! (0 !N) ⇒ (0 !N)   <  mkℤ 1 ff ]  0 ! (0 !N) ⇒ (1 !N)
ex6 = Fun{j = toℤ 1} refl refl (NatRefl refl) (NatRefl refl)

ex7 : 2 ! (0 !N) ⇒ (0 !N)   < mkℤ 1 tt ] 0 ! (1 !N) ⇒ (1 !N)
ex7 = Fun{j = toℤ 1} refl refl (NatRefl refl) (NatRefl refl)

ex8 : 0 ! (0 !N) ⇒ (0 !N)   < 0ℤ ] 0 ! (1 !N) ⇒ (1 !N)
ex8 = Fun{j = toℤ 1} refl refl (NatRefl refl) (NatRefl refl)

ex8a : 0 ! (0 !N) ⇒ (0 !N)   < 0ℤ ] 0 ! (0 !N) ⇒ (1 !N)
ex8a = Fun{j = toℤ 0} refl refl (NatRefl refl) (NatRefl refl)

ex8b : 0 ! (0 !N) ⇒ (0 !N)   < 0ℤ ] 0 ! (2 !N) ⇒ (2 !N)
ex8b = Fun{j = toℤ 2} refl refl (NatRefl refl) (NatRefl refl)

ex8c : 0 ! (0 !N) ⇒ (0 !N)   < 0ℤ ] 0 ! (1 !N) ⇒ (2 !N)
ex8c = Fun{j = toℤ 1} refl refl (NatRefl refl) (NatRefl refl)

ex8d : 0 ! (0 !N) ⇒ (0 !N)   < toℤ 2 ] 0 ! (2 !N) ⇒ (2 !N)
ex8d = Fun{j = toℤ 2} refl refl (NatRefl refl) (NatRefl refl)

ex8e : 0 ! (0 !N) ⇒ (0 !N)   < toℤ 1 ] 0 ! (2 !N) ⇒ (2 !N)
ex8e = Fun{j = toℤ 2} refl refl (NatRefl refl) (NatRefl refl)

ex8f : 0 ! (0 !N) ⇒ (0 !N)   < toℤ 1 ] 0 ! (3 !N) ⇒ (3 !N)
ex8f = Fun{j = toℤ 3} refl refl (NatRefl refl) (NatRefl refl)

ex8g : 0 ! (1 !N) ⇒ (1 !N)   < toℤ 1 ] 0 ! (0 !N) ⇒ (0 !N)
ex8g = Fun {!!} {!!} {!!} {!!} 

{-
ex8g : 2 ! (0 !N) ⇒ (0 !N)   < toℤ 1 ] 0 ! (0 !N) ⇒ (0 !N)
ex8g = Fun{j = toℤ 1} {!!} {!!} {!!} {!!}
-}