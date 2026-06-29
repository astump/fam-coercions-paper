module Coherence where

open import lib
open import Tp
open import Declarative
open import Decproc
open import DecprocTrans
open import Semantics
open import Completeness
open import Soundness

-- Equivalence of declarative coercions, modulo the monad laws
-- See fmap/Decl.agda
infix 4 _≃_
data _≃_ : {A B : Tp} → A <: B → A <: B → Set where
  -- Equivalence-relation rules.
  ≃-refl  : ∀ {A B} (d : A <: B) → d ≃ d

  ≃-sym   : ∀ {A B} {d₁ d₂ : A <: B}
            → d₁ ≃ d₂
            → d₂ ≃ d₁

  ≃-trans : ∀ {A B} {d₁ d₂ d₃ : A <: B}
            → d₁ ≃ d₂ → d₂ ≃ d₃
            → d₁ ≃ d₃

  -- Congruence for each constructor with sub-derivations.
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

  -- TODO: Add monad/applicative/functor laws, e.g.
  --   Left identity   (return a >>= h = h a)
  --   Right identity  (m >>= return = m)
  --   Associativity   ((m >>= g) >>= h = m >>= (λ x → g x >>= h))

-- Congruence for nat-sound
nat-cong : ∀ {b b' : 𝔹} (ok₁ ok₂ : layerOK b b' ≡ tt)
           → nat-sound ok₁ ≃ nat-sound ok₂
nat-cong {ff} {ff} refl refl = ≃-refl _
nat-cong {ff} {tt} refl refl = ≃-refl _
nat-cong {tt} {tt} refl refl = ≃-refl _
nat-cong {tt} {ff} () _

-- Congruence for funOrd-sound
funOrd-cong : ∀ {b b' : 𝔹} {A B A' B' : Tp!}
              (ok₁ ok₂ : layerOK b b' ≡ tt)
              {dom₁ dom₂ : ⟦ A' ⟧ <: ⟦ A ⟧}
              {cod₁ cod₂ : ⟦ B ⟧ <: ⟦ B' ⟧}
              → dom₁ ≃ dom₂ → cod₁ ≃ cod₂
              → funOrd-sound ok₁ dom₁ cod₁ ≃ funOrd-sound ok₂ dom₂ cod₂
funOrd-cong {ff} {ff} ok₁ ok₂ domeq codeq = ≃-cong-Fun domeq codeq
funOrd-cong {ff} {tt} ok₁ ok₂ domeq codeq = ≃-cong-Trans (≃-cong-Fun domeq codeq) (≃-refl _)
funOrd-cong {tt} {ff} () _ domeq codeq
funOrd-cong {tt} {tt} ok₁ ok₂ domeq codeq = ≃-cong-Cov (≃-cong-Fun domeq codeq)

-- Congruence for seq-core-sound
seq-core-cong : ∀ {A B A' B' : Tp!}
                {dom₁ dom₂ : ⟦ A' ⟧ <: ⟦ ↑ A ⟧}
                {cod₁ cod₂ : ⟦ ↑ B ⟧ <: ⟦ B' ⟧}
                → dom₁ ≃ dom₂ → cod₁ ≃ cod₂
                → seq-core-sound {A} {B} dom₁ cod₁ ≃ seq-core-sound {A} {B} dom₂ cod₂
seq-core-cong domeq codeq =
  ≃-cong-Trans (≃-refl Seq)
    (≃-cong-Fun (≃-cong-Trans domeq (≃-refl _))
                (≃-cong-Trans (≃-refl _) codeq))

-- Congruence for funSeq-sound
funSeq-cong : ∀ {b b' : 𝔹} {A B A' B' : Tp!}
              {dom₁ dom₂ : ⟦ A' ⟧ <: ⟦ ↑ A ⟧}
              {cod₁ cod₂ : ⟦ ↑ B ⟧ <: ⟦ B' ⟧}
              → dom₁ ≃ dom₂ → cod₁ ≃ cod₂
              → funSeq-sound {b} {b'} {A} {B} dom₁ cod₁ ≃ funSeq-sound {b} {b'} dom₂ cod₂
funSeq-cong {ff} {ff} domeq codeq = ≃-cong-Trans (≃-refl _) (seq-core-cong domeq codeq)
funSeq-cong {ff} {tt} domeq codeq =
  ≃-cong-Trans (≃-cong-Trans (≃-refl _) (seq-core-cong domeq codeq)) (≃-refl _)
funSeq-cong {tt} {ff} domeq codeq = seq-core-cong domeq codeq
funSeq-cong {tt} {tt} domeq codeq = ≃-cong-Trans (seq-core-cong domeq codeq) (≃-refl _)

-- sound! of reflexivity is ≃ the declarative reflexivity
sound!-refl : ∀ {A : Tp!} → sound! (refl! {A}) ≃ refl-raw {⟦ A ⟧}
sound!-refl {ff !N}      = ≃-refl _
sound!-refl {tt !N}      = ≃-refl _
sound!-refl {ff ! A ⇒ B} = ≃-cong-Fun sound!-refl sound!-refl
sound!-refl {tt ! A ⇒ B} = ≃-cong-Cov (≃-cong-Fun sound!-refl sound!-refl)

-- The ordinary and sequenced rules agree, provided their sub-coercions are related by pure!.
fun-pure-seq : ∀ {b b' : 𝔹} {A B A' B' : Tp!}
               (ok   : layerOK b b' ≡ tt)
               (dom  : ⟦ A' ⟧ <: ⟦ A ⟧)  (dom' : ⟦ A' ⟧ <: ⟦ ↑ A ⟧)
               (cod  : ⟦ B  ⟧ <: ⟦ B' ⟧) (cod' : ⟦ ↑ B ⟧ <: ⟦ B' ⟧)
               → Trans dom (sound! (pure! {A})) ≃ dom'
               → Trans (sound! (pure! {B})) cod' ≃ cod
               → funOrd-sound ok dom cod ≃ funSeq-sound dom' cod'
fun-pure-seq ok dom dom' cod cod' hyp-dom hyp-cod = {!!}

-- Uniqueness of algorithmic coercions (up to ≃)
-- Any two derivations of `A <:! B` have ≃-equal soundness images.
-- Note this can only hold up to `≃`, not `≡`, because the FunOrd/FunSeq rules overlap.
sound!-unique : ∀ {A B : Tp!} (d₁ d₂ : A <:! B) → sound! d₁ ≃ sound! d₂

-- mutually recursive lemmas
pure-dom-coh : ∀ {A' A : Tp!} (d₁ : A' <:! A) (d₂ : A' <:! ↑ A)
               → Trans (sound! d₁) (sound! (pure! {A})) ≃ sound! d₂
pure-cod-coh : ∀ {B B' : Tp!} (d₂ : ↑ B <:! B') (d₁ : B <:! B')
               → Trans (sound! (pure! {B})) (sound! d₂) ≃ sound! d₁

-- Both Nat!
sound!-unique (Nat! ok₁) (Nat! ok₂) = nat-cong ok₁ ok₂
-- Both FunOrd!
sound!-unique (FunOrd! ok₁ dom₁ cod₁) (FunOrd! ok₂ dom₂ cod₂) =
  funOrd-cong ok₁ ok₂ (sound!-unique dom₁ dom₂) (sound!-unique cod₁ cod₂)
-- Both FunSeq!
sound!-unique (FunSeq! dom₁ cod₁) (FunSeq! dom₂ cod₂) =
  funSeq-cong (sound!-unique dom₁ dom₂) (sound!-unique cod₁ cod₂)
-- Mixed: ordinary vs sequenced (b = tt, b' = ff is impossible).
sound!-unique (FunOrd! {b = tt} {b' = ff} () _ _) (FunSeq! _ _)
sound!-unique (FunOrd! {A = A} {B = B} ok₁ dom₁ cod₁) (FunSeq! dom₂ cod₂) =
  fun-pure-seq ok₁ (sound! dom₁) (sound! dom₂) (sound! cod₁) (sound! cod₂)
               (pure-dom-coh dom₁ dom₂)
               (pure-cod-coh cod₂ cod₁)
-- Mixed: sequenced vs ordinary — the symmetric image of the above.
sound!-unique (FunSeq! _ _) (FunOrd! {b = tt} {b' = ff} () _ _)
sound!-unique (FunSeq! dom₁ cod₁) (FunOrd! {A = A} {B = B} ok₂ dom₂ cod₂) =
  ≃-sym (fun-pure-seq ok₂ (sound! dom₂) (sound! dom₁) (sound! cod₂) (sound! cod₁)
                      (pure-dom-coh dom₂ dom₁)
                      (pure-cod-coh cod₁ cod₂))

pure-dom-coh d₁ d₂ = {!!}
pure-cod-coh d₂ d₁ = {!!}

-- Uniqueness lifted to source types via `sound!'`.
-- sound!' d = Trans (raw<norm A) (Trans (sound! d) (norm<raw B)).
sound!'-unique : ∀ {A B : Tp} (d₁ d₂ : ⌈ A ⌉ <:! ⌈ B ⌉) → sound!' {A} {B} d₁ ≃ sound!' {A} {B} d₂
sound!'-unique d₁ d₂ =
  ≃-cong-Trans (≃-refl _)
    (≃-cong-Trans (sound!-unique d₁ d₂) (≃-refl _))

-- Running a declarative derivation through completeness and back through
-- soundness yields a ≃-equivalent derivation.
-- See reify-eval in agda/fmap/Fmap.agda
round-trip : ∀ {A B : Tp} (d : A <: B) → d ≃ sound!' (complete! d)
round-trip d = {!!}

coherence : ∀ {A B : Tp} (d₁ d₂ : A <: B) → d₁ ≃ d₂
coherence d₁ d₂ =
  ≃-trans (round-trip d₁)
  (≃-trans (sound!'-unique (complete! d₁) (complete! d₂))
           (≃-sym (round-trip d₂)))
