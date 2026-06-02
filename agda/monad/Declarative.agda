module Declarative where

open import lib
open import Tp

-- Declarative relation on Tp

infix 5 _<:_

data _<:_ : Tp → Tp → Set where
  NatRefl : N <: N

  Fun : ∀{T1 T2 T1' T2' : Tp} → 
        T1' <: T1 →
        T2  <: T2' →
        T1 ⇒ T2 <: T1' ⇒ T2'

  Seq : ∀{T1 T2 : Tp} →
        L (T1 ⇒ T2) <: L T1 ⇒ L T2

  Pure : ∀{T : Tp} →
         T <: L T

  Cov : ∀{T1 T2 : Tp} →
        T1 <: T2 →
        L T1 <: L T2

  Join : ∀{T : Tp} →
         L (L T) <: L T

  Trans : ∀{T1 T2 T3 : Tp} →
          T1 <: T2 →
          T2 <: T3 →
          T1 <: T3

-- Reflexivity is admissible for the declarative relation.
refl-raw : ∀{T} → T <: T
refl-raw {N}      = NatRefl
refl-raw {L T}    = Cov refl-raw
refl-raw {T ⇒ T'} = Fun refl-raw refl-raw

-- ↑T = L T
infix 30 ↑_
↑_ : Tp! → Tp!
↑ (_ !N)      = tt !N
↑ (_ ! A ⇒ B) = tt ! A ⇒ B

-- If tt, force a positive L
bump! : 𝔹 → Tp! → Tp!
bump! ff A = A
bump! tt  A = ↑ A

-- the only impossible coersion is L T <: T
layerOK : 𝔹 → 𝔹 → 𝔹
layerOK tt ff = ff
layerOK _ _ = tt

-- function-rule outer condidtion
funOK : 𝔹 → 𝔹 → 𝔹 → 𝔹
funOK ff b b' = layerOK b b'
funOK tt  b b' = tt

-- New relation on Tp!
infix 5 _<:!_

data _<:!_ : Tp! → Tp! → Set where
  Nat<! : ∀ {b b' : 𝔹} →
          layerOK b b' ≡ tt →
          (b !N) <:! (b' !N)

  {- Function rule

  if q = ff, this is the ordinary function rule.
  Input
    A' <: A
    B  <: B'
  Output
    b! A ⇒ B <: b'! A' ⇒ B'
    so long as  ¬(b ≡ T ∧ b' ≡ F)

  If q = tt, this is a Seq-shaped rule.
  Input
    A'  <: L A
    L B <: B'
  Output
    b! A ⇒ B <: b'! A' ⇒ B'
    For all b b'
  -}
  Fun<! : ∀ {q b b' : 𝔹}
           {A B A' B' : Tp!} →
          funOK q b b' ≡ tt →
          A' <:! bump! q A →
          bump! q B <:! B' →
          (b ! A ⇒ B) <:! (b' ! A' ⇒ B')

-- Reflexivity is admissible
<:!-refl : ∀ {A : Tp!} → A <:! A
<:!-refl {ff !N} = Nat<! refl
<:!-refl {tt  !N} = Nat<! refl
<:!-refl {ff ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl (<:!-refl {A = B})
<:!-refl {tt  ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl (<:!-refl {A = B})

-- interpret a Tp! as a Tp (Denotation)
infix 100 ⟦_⟧

⟦_⟧ : Tp! → Tp
⟦ ff !N ⟧ = N
⟦ tt  !N ⟧ = L N
⟦ ff ! A ⇒ B ⟧ = ⟦ A ⟧ ⇒ ⟦ B ⟧
⟦ tt  ! A ⇒ B ⟧ = L (⟦ A ⟧ ⇒ ⟦ B ⟧)

-- normalize a Tp as a Tp!
infix 100 ⌈_⌉

⌈_⌉ : Tp → Tp!
⌈ N ⌉       = ff !N
⌈ L T ⌉     = ↑ ⌈ T ⌉
⌈ T ⇒ T' ⌉  = ff ! ⌈ T ⌉ ⇒ ⌈ T' ⌉

-- Soundness

nat-sound : ∀ {b b' : 𝔹} →
            layerOK b b' ≡ tt →
            ⟦ b !N ⟧ <: ⟦ b' !N ⟧
nat-sound {ff} {ff} refl = refl-raw
nat-sound {ff} {tt} refl = Pure
nat-sound {tt} {tt} refl = refl-raw
nat-sound {tt} {ff} ()

-- ⟦ ↑ A⟧ <: L ⟦ A ⟧
↑<L⟦⟧ : ∀ (A : Tp!) → ⟦ ↑ A ⟧ <: L ⟦ A ⟧
↑<L⟦⟧ (ff !N) = refl-raw
↑<L⟦⟧ (tt  !N) = Pure
↑<L⟦⟧ (ff ! A ⇒ B) = refl-raw
↑<L⟦⟧ (tt !  A ⇒ B) = Pure

-- L ⟦ A ⟧ <: ⟦ ↑ A ⟧
L⟦⟧<↑ : ∀ (A : Tp!) → L ⟦ A ⟧ <: ⟦ ↑ A ⟧
L⟦⟧<↑ (ff !N) = refl-raw
L⟦⟧<↑ (tt  !N) = Join
L⟦⟧<↑ (ff ! A ⇒ B) = refl-raw
L⟦⟧<↑ (tt  ! A ⇒ B) = Join

-- Soundness for ordinary function rule (not seq shaped)
funOrd-sound : ∀ {b b' : 𝔹} {A B A' B' : Tp!} →
               layerOK b b' ≡ tt →
               ⟦ A' ⟧ <: ⟦ A ⟧ →
               ⟦ B  ⟧ <: ⟦ B' ⟧ →
               ⟦ b ! A ⇒ B ⟧ <: ⟦ b' ! A' ⇒ B' ⟧
funOrd-sound {ff} {ff} ok dom cod =
  Fun dom cod
funOrd-sound {ff} {tt} ok dom cod =
  Trans (Fun dom cod) Pure
funOrd-sound {tt} {ff} () dom cod
funOrd-sound {tt} {tt} ok dom cod =
  Cov (Fun dom cod)

-- Soundness for Seq-shaped function rule where b, b' = ff
seq-core-sound : ∀ {A B A' B' : Tp!} →
                 ⟦ A' ⟧ <: ⟦ ↑ A ⟧ →
                 ⟦ ↑ B ⟧ <: ⟦ B' ⟧ →
                 L (⟦ A ⟧ ⇒ ⟦ B ⟧) <: ⟦ A' ⟧ ⇒ ⟦ B' ⟧
seq-core-sound {A} {B} dom cod =
  Trans Seq
    (Fun (Trans dom (↑<L⟦⟧ A))
         (Trans (L⟦⟧<↑ B) cod))

-- Soundness for the full Seq-shaped fun rule
funSeq-sound : ∀ {b b' : 𝔹} {A B A' B' : Tp!} →
               ⟦ A' ⟧ <: ⟦ ↑ A ⟧ →
               ⟦ ↑ B ⟧ <: ⟦ B' ⟧ →
               ⟦ b ! A ⇒ B ⟧ <: ⟦ b' ! A' ⇒ B' ⟧
funSeq-sound {ff} {ff} dom cod =
  Trans Pure (seq-core-sound dom cod)
funSeq-sound {ff} {tt} dom cod =
  Trans (Trans Pure (seq-core-sound dom cod)) Pure
funSeq-sound {tt} {ff} dom cod =
  seq-core-sound dom cod
funSeq-sound {tt} {tt} dom cod =
  Trans (seq-core-sound dom cod) Pure

-- Main soundness theorem
sound! : ∀ {A B : Tp!} → A <:! B → ⟦ A ⟧ <: ⟦ B ⟧
sound! (Nat<! ok) =
  nat-sound ok
sound! (Fun<! {q = ff} ok dom cod) =
  funOrd-sound ok (sound! dom) (sound! cod)
sound! (Fun<! {q = tt} ok dom cod) =
  funSeq-sound (sound! dom) (sound! cod)

-- T =: ⟦ ⌈ T ⌉ ⟧
mutual
  raw<norm : ∀ (T : Tp) → T <: ⟦ ⌈ T ⌉ ⟧
  raw<norm N = NatRefl
  raw<norm (L T) =
    Trans (Cov (raw<norm T))
          (L⟦⟧<↑ ⌈ T ⌉)
  raw<norm (T ⇒ U) =
    Fun (norm<raw T)
        (raw<norm U)

  norm<raw : ∀ (T : Tp) → ⟦ ⌈ T ⌉ ⟧ <: T
  norm<raw N = NatRefl
  norm<raw (L T) =
    Trans (↑<L⟦⟧ ⌈ T ⌉)
          (Cov (norm<raw T))
  norm<raw (T ⇒ U) =
    Fun (raw<norm T)
        (norm<raw U)

-- completeness for pure
pure! : ∀ {A : Tp!} → A <:! ↑ A
pure! {ff !N} = Nat<! refl
pure! {tt  !N} = Nat<! refl
pure! {ff ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl <:!-refl
pure! {tt ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl <:!-refl

-- completeness for join
join! : ∀ {A : Tp!} → ↑ (↑ A) <:! ↑ A
join! {ff !N} = Nat<! refl
join! {tt  !N} = Nat<! refl
join! {ff ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl <:!-refl
join! {tt ! A ⇒ B} =
  Fun<! {q = ff} refl <:!-refl <:!-refl

-- completeness for cov
cov! : ∀ {A B : Tp!} → A <:! B → ↑ A <:! ↑ B
cov! (Nat<! ok) =
  Nat<! refl
cov! (Fun<! {q = tt} ok dom cod) =
  Fun<! {q = tt} refl dom cod
cov! (Fun<! {q = ff} ok dom cod) =
  Fun<! {q = ff} refl dom cod

-- completeness for Seq
seq! : ∀ {A B : Tp!} →
       (tt ! A ⇒ B) <:! (ff ! ↑ A ⇒ ↑ B)
seq! =
  Fun<! {q = tt}
        refl
        <:!-refl
        <:!-refl

-- Completeness for Trans

layerOK-trans : ∀ (b₁ b₂ b₃ : 𝔹) →
                layerOK b₁ b₂ ≡ tt →
                layerOK b₂ b₃ ≡ tt →
                layerOK b₁ b₃ ≡ tt
layerOK-trans ff b₂    b₃    p q = refl
layerOK-trans tt  ff b₃    ()
layerOK-trans tt  tt  ff p ()
layerOK-trans tt  tt  tt  p q = refl

{-# TERMINATING #-}
trans! : ∀ {A B C : Tp!} →
         A <:! B →
         B <:! C →
         A <:! C
-- Atomic case.
trans!
  (Nat<! {b = b₁} {b' = b₂} ok₁)
  (Nat<! {b = .b₂} {b' = b₃} ok₂) =
  Nat<! (layerOK-trans b₁ b₂ b₃ ok₁ ok₂)

-- Ordinary followed by ordinary.
trans!
  (Fun<! {q = ff}
         {b = b₁} {b' = b₂}
         {A = A₁} {B = B₁}
         {A' = A₂} {B' = B₂}
         ok₁ dom₁ cod₁)
  (Fun<! {q = ff}
         {b = .b₂} {b' = b₃}
         {A = .A₂} {B = .B₂}
         {A' = A₃} {B' = B₃}
         ok₂ dom₂ cod₂) =
  Fun<! {q = ff}
        {b = b₁} {b' = b₃}
        {A = A₁} {B = B₁}
        {A' = A₃} {B' = B₃}
        (layerOK-trans b₁ b₂ b₃ ok₁ ok₂)
        (trans! dom₂ dom₁)
        (trans! cod₁ cod₂)

-- Ordinary followed by Seq-shaped.
trans!
  (Fun<! {q = ff} ok₁ dom₁ cod₁)
  (Fun<! {q = tt} ok₂ dom₂ cod₂) =
  Fun<! {q = tt}
    refl
    (trans! dom₂ ((cov! dom₁)))
    (trans! ((cov! cod₁)) cod₂)

-- Seq-shaped followed by ordinary.
trans!
  (Fun<! {q = tt} ok₁ dom₁ cod₁)
  (Fun<! {q = ff} ok₂ dom₂ cod₂) =
  Fun<! {q = tt}
    refl
    (trans! dom₂ dom₁)
    (trans! cod₁ cod₂)

-- Seq-shaped followed by Seq-shaped.
trans!
  (Fun<! {q = tt} ok₁ dom₁ cod₁)
  (Fun<! {q = tt} ok₂ dom₂ cod₂) =
  Fun<! {q = tt}
    refl
    (trans! dom₂ (trans! (cov! dom₁) join! ))
    (trans! (trans! cod₁ pure!) cod₂)


-- Full Completeness
complete! : ∀ {A B : Tp} → A <: B → ⌈ A ⌉ <:! ⌈ B ⌉
complete! NatRefl =
  Nat<! refl

complete! (Fun dom cod) =
  Fun<! {q = ff} refl
        (complete! dom)
        (complete! cod)

complete! Seq =
  seq!

complete! Pure =
  pure!

complete! (Cov p) =
  cov! (complete! p)

complete! Join =
  join!

complete! (Trans p q) = trans! (complete! p) (complete! q)
