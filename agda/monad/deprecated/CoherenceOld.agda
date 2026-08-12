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

  ≃-unitL : ∀ {A B} {d : A <: B} → Trans refl-raw d ≃ d
  ≃-unitR : ∀ {A B} {d : A <: B} → Trans d refl-raw ≃ d

  -- Trans is associative.
  ≃-assoc : ∀ {A B C D} {d₁ : A <: B} {d₂ : B <: C} {d₃ : C <: D}
            → Trans (Trans d₁ d₂) d₃ ≃ Trans d₁ (Trans d₂ d₃)

  -- Naturality of Pure
  ≃-Pure-nat : ∀ {A B} {d : A <: B} → Trans d Pure ≃ Trans Pure (Cov d)

  ≃-Pure-Join-Cov : ∀ {A} → Trans (Pure {L A}) (Join {A}) ≃ Cov (refl-raw {A})
  -- TODO: Add the remaining monad/applicative/functor laws

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

-- reused lemma
sound-pure-arr : ∀ {A B : Tp!} → sound! (pure! {ff ! A ⇒ B}) ≃ Pure
sound-pure-arr =
  ≃-trans (≃-cong-Trans (≃-cong-Fun sound!-refl sound!-refl) (≃-refl _)) ≃-unitL

-- another usefull lemma
sound-pure-arrL : ∀ {A B : Tp!} → sound! (pure! {tt ! A ⇒ B}) ≃ refl-raw {⟦ tt ! A ⇒ B ⟧}
sound-pure-arrL = ≃-cong-Cov (≃-cong-Fun sound!-refl sound!-refl)

-- helper for fun-pure-seq
pure-↑<L : ∀ {A : Tp!} → Trans (sound! (pure! {A})) (↑<L⟦⟧ A) ≃ Pure
pure-↑<L {tt !N} = ≃-unitL
pure-↑<L {ff !N} = ≃-unitR
pure-↑<L {tt ! A ⇒ A₁} =
  ≃-trans (≃-cong-Trans sound-pure-arrL (≃-refl _)) ≃-unitL
pure-↑<L {ff ! A ⇒ A₁} =
  ≃-trans (≃-cong-Trans sound-pure-arr (≃-refl _)) ≃-unitR

-- helper for fun-pure-seq
pure-L⟦⟧<↑ : ∀ {B : Tp!} → Trans Pure (L⟦⟧<↑ B) ≃ sound! (pure! {B})
-- Trans Pure Join ≃ Cov NatRefl
pure-L⟦⟧<↑ {tt !N} = ≃-Pure-Join-Cov
pure-L⟦⟧<↑ {ff !N} = ≃-unitR
pure-L⟦⟧<↑ {tt ! B ⇒ B₁} =
  ≃-trans ≃-Pure-Join-Cov (≃-sym sound-pure-arrL)
pure-L⟦⟧<↑ {ff ! B ⇒ B₁} =
  ≃-trans ≃-unitR (≃-sym sound-pure-arr)


-- The ordinary and sequenced rules agree, provided their sub-coercions are related by pure!.
fun-pure-seq : ∀ {b b' : 𝔹} {A B A' B' : Tp!}
               (ok   : layerOK b b' ≡ tt)
               (dom  : ⟦ A' ⟧ <: ⟦ A ⟧)  (dom' : ⟦ A' ⟧ <: ⟦ ↑ A ⟧)
               (cod  : ⟦ B  ⟧ <: ⟦ B' ⟧) (cod' : ⟦ ↑ B ⟧ <: ⟦ B' ⟧)
               → Trans dom (sound! (pure! {A})) ≃ dom'
               → Trans (sound! (pure! {B})) cod' ≃ cod
               → funOrd-sound ok dom cod ≃ funSeq-sound dom' cod'
-- Trans
--   (Trans
--     Seq
--     (Fun
--       (Trans
--         (Trans
--           dom
--           (sound! pure!))
--         (↑<L⟦⟧ A))
--       (Trans (L⟦⟧<↑ B) cod')))
--   Pure
--  ≃
--  Cov (Fun
--         dom
--         (Trans
--           (sound! pure!)
--           cod'))
fun-pure-seq {tt} {tt} ok dom dom' cod cod' hyp-dom hyp-cod =
  ≃-trans
    (≃-cong-Cov (≃-cong-Fun (≃-refl _) (≃-sym hyp-cod)))
    (≃-sym (≃-trans (≃-cong-Trans (seq-core-cong (≃-sym hyp-dom) (≃-refl _)) (≃-refl _))
      {!!}))
-- Trans
--   Pure
--   (Trans
--     Seq
--     (Fun
--       (Trans
--         (Trans
--           dom
--           (sound! pure!))
--         (↑<L⟦⟧ A))
--       (Trans
--         (L⟦⟧<↑ B)
--         cod')))
-- ≃
-- Fun
--   dom
--   (Trans
--     (sound! pure!)
--     cod')
fun-pure-seq {ff} {tt} ok dom dom' cod cod' hyp-dom hyp-cod = 
  ≃-trans
    (≃-cong-Trans (≃-cong-Fun (≃-refl _) (≃-sym hyp-cod)) (≃-refl _))
    (≃-sym (≃-trans
      (≃-cong-Trans (≃-cong-Trans (≃-refl _) (seq-core-cong (≃-sym hyp-dom) (≃-refl _))) (≃-refl _))
      (≃-cong-Trans
        {!!}
        (≃-refl _))))
-- same hole as above
fun-pure-seq {ff} {ff} ok dom dom' cod cod' hyp-dom hyp-cod = 
  ≃-trans
    (≃-cong-Fun (≃-refl _) (≃-sym hyp-cod))
    (≃-sym (≃-trans
      (≃-cong-Trans (≃-refl _) (seq-core-cong (≃-sym hyp-dom) (≃-refl _)))
      {!!}))
-- Helper for pure-dom-coh
funOrd-pure : ∀ {b q : 𝔹} {A B A' B' : Tp!}
              (ok : layerOK b q ≡ tt)
              (dom : ⟦ A' ⟧ <: ⟦ A ⟧) (cod : ⟦ B ⟧ <: ⟦ B' ⟧)
              → Trans (funOrd-sound ok dom cod) (sound! (pure! {q ! A' ⇒ B'}))
                ≃ funOrd-sound {b} {tt} (layerOK-tt {b}) dom cod
-- q = tt: pure! is the identity up to ≃, so use unitR
funOrd-pure {tt} {tt} ok dom cod =
  ≃-trans (≃-cong-Trans (≃-refl _) sound-pure-arrL) ≃-unitR
-- same as above: split needed to reduce layerOK-tt
funOrd-pure {ff} {tt} ok dom cod =
  ≃-trans (≃-cong-Trans (≃-refl _) sound-pure-arrL) ≃-unitR
funOrd-pure {ff} {ff} ok dom cod =
  ≃-cong-Trans (≃-refl _) sound-pure-arr

-- Helper for pure-dom-coh
funSeq-pure : ∀ {b q : 𝔹} {A B A' B' : Tp!}
              (dom : ⟦ A' ⟧ <: ⟦ ↑ A ⟧) (cod : ⟦ ↑ B ⟧ <: ⟦ B' ⟧)
              → Trans (funSeq-sound dom cod) (sound! (pure! {q ! A' ⇒ B'}))
                ≃ funSeq-sound {b} {tt} dom cod
-- q = tt: pure! is the identity up to ≃, so use unitR
funSeq-pure {q = tt} dom cod =
  ≃-trans (≃-cong-Trans (≃-refl _) sound-pure-arrL) ≃-unitR
funSeq-pure {tt} {q = ff} dom cod =
  ≃-cong-Trans (≃-refl _) sound-pure-arr
funSeq-pure {ff} {q = ff} dom cod =
  ≃-cong-Trans (≃-refl _) sound-pure-arr

-- Helper for pure-cod-coh
-- Like funOrd-pure, but pure! is on the left
-- Needs ≃-Pure-nat
pure-funOrd : ∀ {b₀ b' : 𝔹} {A B A' B' : Tp!}
              (ok : layerOK tt b' ≡ tt)
              (dom : ⟦ A' ⟧ <: ⟦ A ⟧) (cod : ⟦ B ⟧ <: ⟦ B' ⟧)
              → Trans (sound! (pure! {b₀ ! A ⇒ B})) (funOrd-sound {tt} {b'} ok dom cod)
                ≃ funOrd-sound {b₀} {b'} (layerOK-relax ok) dom cod
pure-funOrd {b₀} {ff} () dom cod
pure-funOrd {tt} {tt} ok dom cod =
  ≃-trans (≃-cong-Trans sound-pure-arrL (≃-refl _)) ≃-unitL
pure-funOrd {ff} {tt} ok dom cod =
  ≃-trans (≃-cong-Trans sound-pure-arr (≃-refl _)) (≃-sym ≃-Pure-nat)

-- Helper for pure-cod-coh, needs ≃-assoc.
pure-funSeq : ∀ {b₀ b' : 𝔹} {A B A' B' : Tp!}
              (dom : ⟦ A' ⟧ <: ⟦ ↑ A ⟧) (cod : ⟦ ↑ B ⟧ <: ⟦ B' ⟧)
              → Trans (sound! (pure! {b₀ ! A ⇒ B})) (funSeq-sound {tt} {b'} dom cod)
                ≃ funSeq-sound {b₀} {b'} dom cod
pure-funSeq {tt} dom cod =
  ≃-trans (≃-cong-Trans sound-pure-arrL (≃-refl _)) ≃-unitL
pure-funSeq {ff} {ff} dom cod =
  ≃-cong-Trans sound-pure-arr (≃-refl _)
pure-funSeq {ff} {tt} dom cod =
  ≃-trans (≃-cong-Trans sound-pure-arr (≃-refl _)) (≃-sym ≃-assoc)

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

pure-dom-coh (Nat! {b = ff} {b' = ff} refl) (Nat! refl) = ≃-unitL
pure-dom-coh (Nat! {b = ff} {b' = tt} refl) (Nat! refl) = ≃-unitR
pure-dom-coh (Nat! {b = tt} {b' = tt} refl) (Nat! refl) = ≃-unitL
pure-dom-coh (FunOrd! x d₁ d₃) (FunOrd! x₁ d₂ d₄) =
  ≃-trans
    (funOrd-pure x (sound! d₁) (sound! d₃))
    (funOrd-cong layerOK-tt x₁ (sound!-unique d₁ d₂) (sound!-unique d₃ d₄))
pure-dom-coh (FunSeq! d₁ d₃) (FunSeq! d₂ d₄) =
  ≃-trans
    (funSeq-pure (sound! d₁) (sound! d₃))
    (funSeq-cong (sound!-unique d₁ d₂) (sound!-unique d₃ d₄))
pure-dom-coh (FunOrd! x d₁ d₃) (FunSeq! d₂ d₄) = 
  ≃-trans
    (funOrd-pure x (sound! d₁) (sound! d₃))
    (fun-pure-seq layerOK-tt (sound! d₁) (sound! d₂) (sound! d₃) (sound! d₄)
      (pure-dom-coh d₁ d₂) (pure-cod-coh d₄ d₃))
pure-dom-coh (FunSeq! d₁ d₃) (FunOrd! x d₂ d₄) = 
  ≃-trans
    (funSeq-pure (sound! d₁) (sound! d₃))
    (≃-sym (fun-pure-seq x (sound! d₂) (sound! d₁) (sound! d₄) (sound! d₃)
      (pure-dom-coh d₂ d₁) (pure-cod-coh d₃ d₄)))

pure-cod-coh (Nat! refl) (Nat! {b = ff} {b' = tt} refl) = ≃-unitR
pure-cod-coh (Nat! refl) (Nat! {b = tt} {b' = tt} refl) = ≃-unitL
pure-cod-coh (FunOrd! x₁ d₂ d₄) (FunOrd! x d₁ d₃) =
  ≃-trans
    (pure-funOrd x₁ (sound! d₂) (sound! d₄))
    (funOrd-cong (layerOK-relax x₁) x (sound!-unique d₂ d₁) (sound!-unique d₄ d₃))
pure-cod-coh (FunSeq! d₂ d₄) (FunSeq! d₁ d₃) =
  ≃-trans
    (pure-funSeq (sound! d₂) (sound! d₄))
    (funSeq-cong (sound!-unique d₂ d₁) (sound!-unique d₄ d₃))
pure-cod-coh (FunSeq! d₂ d₄) (FunOrd! x d₁ d₃) =
  ≃-trans
    (pure-funSeq (sound! d₂) (sound! d₄))
    (≃-sym (fun-pure-seq x (sound! d₁) (sound! d₂) (sound! d₃) (sound! d₄)
      (pure-dom-coh d₁ d₂) (pure-cod-coh d₄ d₃)))
pure-cod-coh (FunOrd! x d₂ d₄) (FunSeq! d₁ d₃) =
  ≃-trans
    (pure-funOrd x (sound! d₂) (sound! d₄))
    (fun-pure-seq (layerOK-relax x) (sound! d₂) (sound! d₁) (sound! d₄) (sound! d₃)
      (pure-dom-coh d₂ d₁) (pure-cod-coh d₃ d₄))

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
