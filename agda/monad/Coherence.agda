module Coherence where

open import lib
open import Tp
open import Declarative
open import Decproc
open import DecprocTrans
open import Semantics
open import Completeness
open import Soundness

-- Equivalence of declarative coercions modulo monad laws
--
-- Two derivations d₁ d₂ : A <: B are equivalent, written d₁ ≃ d₂, if they
-- are equal up to the laws of a monad (which laws?)
--
-- See fmap/Decl.agda
-- Do these need to be justified somehow?
--
-- Note that these rules do not need to be complete, they just need
-- to be sufficient to prove the lemmas below.
--
infix 4 _≃_

data _≃_ : {A B : Tp} → A <: B → A <: B → Set where

  -- Equivalence relation rules

  ≃-refl  : ∀ {A B} (d : A <: B) → d ≃ d

  ≃-sym   : ∀ {A B} {d₁ d₂ : A <: B}
            → d₁ ≃ d₂
            → d₂ ≃ d₁

  ≃-trans : ∀ {A B} {d₁ d₂ d₃ : A <: B}
            → d₁ ≃ d₂ → d₂ ≃ d₃
            → d₁ ≃ d₃

  -- Congruence for each constructor that has sub-derivations as arguments

  ≃-cong-Fun   : ∀ {T1 T2 T1' T2'}
                 {d₁ d₁' : T1' <: T1} {d₂ d₂' : T2 <: T2'}
                 → d₁ ≃ d₁' → d₂ ≃ d₂'
                 → Fun d₁ d₂ ≃ Fun d₁' d₂'

  ≃-cong-Cov   : ∀ {A B} {d₁ d₂ : A <: B}
                 → d₁ ≃ d₂
                 → Cov d₁ ≃ Cov d₂

  ≃-cong-Trans : ∀ {A B C}
                 {d₁ d₁' : A <: B} {d₂ d₂' : B <: C}
                 → d₁ ≃ d₁' → d₂ ≃ d₂'
                 → Trans d₁ d₂ ≃ Trans d₁' d₂'

  -- Monad Laws (what laws exactly?)

  -- x >>= f =
  -- Left identity:
  -- return a >>= h = h a
  --
  -- is this join (Pure a) = a
  -- ≃-monad-unit-l : ∀ {A} → {!!}

  -- Right identity:
  -- m >>= return = m 
  -- ≃-monad-unit-r : ∀ {A} → {!!}

  -- Associativity:
  -- (m >>= g) >>= h = m >>= (λ x → g x >>= h)
  -- ≃-monad-assoc  : ∀ {A} → {!!}

  -- TODO : Add monad laws and applicative laws

-- Helper for sound!-unique: congruence for seq-core-sound
seq-core-cong : ∀ {A B A' B' : Tp!}
                {dom₁ dom₂ : ⟦ A' ⟧ <: ⟦ ↑ A ⟧}
                {cod₁ cod₂ : ⟦ ↑ B ⟧ <: ⟦ B' ⟧}
                → dom₁ ≃ dom₂ → cod₁ ≃ cod₂
                → seq-core-sound {A} {B} dom₁ cod₁ ≃ seq-core-sound {A} {B} dom₂ cod₂
seq-core-cong domeq codeq =
  ≃-cong-Trans (≃-refl Seq)
    (≃-cong-Fun (≃-cong-Trans domeq (≃-refl _))
                (≃-cong-Trans (≃-refl _) codeq))

sound!-trans : ∀ {n : ℕ} {A B C : Tp!}
               (d₁ : A <:! B) (d₂ : B <:! C)
               (ok : size d₁ + size d₂ ≤ n ≡ tt)
               → sound! (trans! d₁ d₂ ok) ≃ Trans (sound! d₁) (sound! d₂)
sound!-trans d₁ d₂ ok = {!!}

-- Helper for sound!-unique: the ordinary and seq-shaped function rules are equivalent.
--
-- funOrd-sound or funSeq-sound take arguments of DIFFERENT types:
--
--   funOrd-sound ok  (dom  : ⟦ A' ⟧ <: ⟦ A  ⟧)  (cod  : ⟦ B  ⟧ <: ⟦ B' ⟧)
--   funSeq-sound     (dom' : ⟦ A' ⟧ <: ⟦ ↑ A ⟧)  (cod' : ⟦ ↑ B ⟧ <: ⟦ B' ⟧)
--
-- They are related by pure! : A <:! ↑ A, whose soundness gives
--   sound! (pure! {A}) : ⟦ A ⟧ <: ⟦ ↑ A ⟧
-- Proof sketch:
--   - case split on b and b' to reduce funOrd-sound and funSeq-sound
--   - substitute with hyp-cod and hyp-dom
--   - close with monad laws (probably add some)
fun-pure-seq : ∀ {b b' : 𝔹} {A B A' B' : Tp!}
               (ok   : layerOK b b' ≡ tt)
               (dom  : ⟦ A' ⟧ <: ⟦ A  ⟧)  (dom' : ⟦ A' ⟧ <: ⟦ ↑ A ⟧)
               (cod  : ⟦ B  ⟧ <: ⟦ B' ⟧)  (cod' : ⟦ ↑ B ⟧ <: ⟦ B' ⟧)
               → Trans dom (sound! (pure! {A})) ≃ dom'
               → Trans (sound! (pure! {B})) cod' ≃ cod
               → funOrd-sound ok dom cod ≃ funSeq-sound dom' cod'
fun-pure-seq ok dom dom' cod cod' hyp-dom hyp-cod = {!!}

-- Uniqueness:
--
-- Any two proofs of A <:! B are propositionally equal.  

-- Counterexample
-- Fun<! {q} refl <:!-refl <:!-refl 
-- proves (ff ! tt! N ⇒ tt ! N) <:! (ff ! tt! N ⇒ tt ! N) with q =ff and q = tt
--
-- So we weaken uniqueness
sound!-unique : ∀ {A B : Tp!} (d₁ d₂ : A <:! B) → sound! d₁ ≃ sound! d₂
sound!-unique (Nat<! {b = ff} {b' = ff} refl) (Nat<! refl) = ≃-refl _
sound!-unique (Nat<! {b = ff} {b' = tt} refl) (Nat<! refl) = ≃-refl _
sound!-unique (Nat<! {b = tt} {b' = tt} refl) (Nat<! refl) = ≃-refl _

-- Both Fun<! with q = f
-- we split on b and b' to reduce the funOrd-sound def, then use congruence + induction

-- b=ff,b'=ff
sound!-unique (Fun<! {q = ff} {b = ff} {b' = ff} refl dom₁ cod₁) (Fun<! {q = ff} refl dom₂ cod₂) =
  ≃-cong-Fun (sound!-unique dom₁ dom₂) (sound!-unique cod₁ cod₂)
-- b=ff,b'=tt
sound!-unique (Fun<! {q = ff} {b = ff} {b' = tt} refl dom₁ cod₁) (Fun<! {q = ff} refl dom₂ cod₂) =
  ≃-cong-Trans (≃-cong-Fun (sound!-unique dom₁ dom₂) (sound!-unique cod₁ cod₂)) (≃-refl _)
-- b=tt,b'=ff: impossible
sound!-unique (Fun<! {q = ff} {b = tt} {b' = ff} () _ _) _
-- b=tt,b'=tt
sound!-unique (Fun<! {q = ff} {b = tt} {b' = tt} refl dom₁ cod₁) (Fun<! {q = ff} refl dom₂ cod₂) =
  ≃-cong-Cov (≃-cong-Fun (sound!-unique dom₁ dom₂) (sound!-unique cod₁ cod₂))

-- Both Fun<! with q = tt
-- split on b and b' to reduce funSeq-sound, then use seq-core-cong + induction.

-- b=ff,b'=ff
sound!-unique (Fun<! {q = tt} {b = ff} {b' = ff} refl dom₁ cod₁) (Fun<! {q = tt} refl dom₂ cod₂) =
  ≃-cong-Trans (≃-refl _) (seq-core-cong (sound!-unique dom₁ dom₂) (sound!-unique cod₁ cod₂))
-- b=ff,b'=tt
sound!-unique (Fun<! {q = tt} {b = ff} {b' = tt} refl dom₁ cod₁) (Fun<! {q = tt} refl dom₂ cod₂) =
  ≃-cong-Trans
    (≃-cong-Trans (≃-refl _) (seq-core-cong (sound!-unique dom₁ dom₂) (sound!-unique cod₁ cod₂)))
    (≃-refl _)
-- b=tt,b'=ff
sound!-unique (Fun<! {q = tt} {b = tt} {b' = ff} refl dom₁ cod₁) (Fun<! {q = tt} refl dom₂ cod₂) =
  seq-core-cong (sound!-unique dom₁ dom₂) (sound!-unique cod₁ cod₂)
-- b=tt,b'=tt
sound!-unique (Fun<! {q = tt} {b = tt} {b' = tt} refl dom₁ cod₁) (Fun<! {q = tt} refl dom₂ cod₂) =
  ≃-cong-Trans (seq-core-cong (sound!-unique dom₁ dom₂) (sound!-unique cod₁ cod₂)) (≃-refl _)

-- Mixed cases: q=ff vs q=tt at the same type (b ! A ⇒ B) <:! (b' ! A' ⇒ B').
--
-- Unfolding sound! gives:
--   funOrd-sound ok₁ (sound! dom₁) (sound! cod₁)  ≃  funSeq-sound (sound! dom₂) (sound! cod₂)
-- where  dom₁ : A' <:! A,  dom₂ : A' <:! ↑A,  cod₁ : B <:! B',  cod₂ : ↑B <:! B'.

-- Only b=tt,b'=ff is impossible (funOK ff tt ff = ff ≠ tt).
sound!-unique (Fun<! {q = ff} {b = tt} {b' = ff} () _ _) (Fun<! {q = tt} _ _ _)

sound!-unique (Fun<! {q = ff} {A = A} {B = B} ok₁ dom₁ cod₁) (Fun<! {q = tt} ok₂ dom₂ cod₂) =
  fun-pure-seq ok₁ (sound! dom₁) (sound! dom₂) (sound! cod₁) (sound! cod₂)
    -- we prove: Trans (sound! dom₁) (sound! (pure! {A})) ≃ sound! dom₂
    -- trans! dom₁ (pure! {A}) has type A' <:! ↑A, same as dom₂,
    -- so sound!-unique gives sound!(trans! dom₁ pure!) ≃ sound! dom₂.
    -- and sound!-trans gives sound!(trans! dom₁ pure!) ≃ Trans (sound! dom₁) (sound! (pure! {A})).
    (≃-trans (≃-sym (sound!-trans dom₁ (pure! {A}) (≤-refl _)))
       (sound!-unique (trans! dom₁ (pure! {A}) (≤-refl _)) dom₂))
    -- We prove: Trans (sound! (pure! {B})) (sound! cod₂) ≃ sound! cod₁
    -- trans! (pure! {B}) cod₂ and cod₁ have the same type B <:! B',
    -- giving Trans (sound! (pure! {B})) (sound! cod₂) ≃ sound! cod₁ by the same route as above.
    (≃-trans (≃-sym (sound!-trans (pure! {B}) cod₂ (≤-refl _)))
             (sound!-unique (trans! (pure! {B}) cod₂ (≤-refl _)) cod₁))

-- Symmetric case: ≃-sym of above
sound!-unique (Fun<! {q = tt} _ _ _) (Fun<! {q = ff} {b = tt} {b' = ff} () _ _)
sound!-unique (Fun<! {q = tt} ok₁ dom₁ cod₁) (Fun<! {q = ff} ok₂ dom₂ cod₂) =
  ≃-sym (sound!-unique (Fun<! {q = ff} ok₂ dom₂ cod₂) (Fun<! {q = tt} ok₁ dom₁ cod₁))

-- use sound!' rather than sound!
-- sound!' d = Trans (raw<norm A) (Trans (sound! d) (norm<raw B)),
sound!'-unique : ∀ {A B : Tp} (d₁ d₂ : ⌈ A ⌉ <:! ⌈ B ⌉) → sound!' d₁ ≃ sound!' d₂
sound!'-unique d₁ d₂ =
  ≃-cong-Trans (≃-refl _)
    (≃-cong-Trans (sound!-unique d₁ d₂) (≃-refl _))

-- Round-trip equivalence
-- 
-- Running a declarative derivation through completeness then through soundness
-- gives a derivation equivalent to the original.
--
-- See reify-eval in agda/fmap/Fmap.agda.

round-trip : ∀ {A B : Tp} (d : A <: B) → d ≃ sound!' (complete! d)
round-trip NatRefl = {!!}
round-trip (Fun dom cod) = {!!}
round-trip Seq = {!!}
round-trip Pure = {!!}
round-trip (Cov p) = {!!}
round-trip Join = {!!}
round-trip (Trans p q) = {!!}

-- Coherence
--
-- Any two declarative derivations of type A <: B are
-- equivalent modulo the monad laws.
--
--   d₁ ≃ sound!' (complete! d₁)     by round-trip
--      = sound!' (complete! d₂)     because unique! gives complete! d₁ ≡ complete! d₂
--   d₂ ≃ sound!' (complete! d₂)     by round-trip
--   Therefore d₁ ≃ d₂ by transitivity of ≃

coherence : ∀ {A B : Tp} (d₁ d₂ : A <: B) → d₁ ≃ d₂
coherence d₁ d₂ =
  ≃-trans (round-trip d₁)
  (≃-trans (sound!'-unique (complete! d₁) (complete! d₂))
           (≃-sym (round-trip d₂)))

