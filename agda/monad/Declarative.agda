open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)

module Declarative where

-- Raw type syntax

infixr 20 _⇒_

data Tp : Set where
  N : Tp
  L : Tp → Tp
  _⇒_ : Tp → Tp → Tp

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

{-
Normalized boolean types

Tp! collapses all applications of L to one boolean flag.

  false !N   means N
  true  !N   means L⁺ N

  false ! A ⇒ B  means A ⇒ B
  true  ! A ⇒ B  means L⁺ (A ⇒ B)
-}

infix 10 _!N
infixr 9 _!_⇒_

data Tp! : Set where
  _!N   : Bool → Tp!
  _!_⇒_ : Bool → Tp! → Tp! → Tp!

-- ↑T = L T
infix 30 ↑_
↑_ : Tp! → Tp!
↑ (_ !N)      = true !N
↑ (_ ! A ⇒ B) = true ! A ⇒ B

-- If true, force a positive L
bump! : Bool → Tp! → Tp!
bump! false A = A
bump! true  A = ↑ A

-- the only impossible coersion is L T <: T
layerOK : Bool → Bool → Bool
layerOK true false = false
layerOK _ _ = true

-- function-rule outer condidtion
funOK : Bool → Bool → Bool → Bool
funOK false b b' = layerOK b b'
funOK true  b b' = true

-- New relation on Tp!
infix 5 _<:!_

data _<:!_ : Tp! → Tp! → Set where
  Nat<! : ∀ {b b' : Bool} →
          layerOK b b' ≡ true →
          (b !N) <:! (b' !N)

  {- Function rule

  if q = false, this is the ordinary function rule.
  Input
    A' <: A
    B  <: B'
  Output
    b! A ⇒ B <: b'! A' ⇒ B'
    so long as  ¬(b ≡ T ∧ b' ≡ F)

  If q = true, this is a Seq-shaped rule.
  Input
    A'  <: L A
    L B <: B'
  Output
    b! A ⇒ B <: b'! A' ⇒ B'
    For all b b'
  -}
  Fun<! : ∀ {q b b' : Bool}
           {A B A' B' : Tp!} →
          funOK q b b' ≡ true →
          A' <:! bump! q A →
          bump! q B <:! B' →
          (b ! A ⇒ B) <:! (b' ! A' ⇒ B')

-- Reflexivity is admissible
<:!-refl : ∀ {A : Tp!} → A <:! A
<:!-refl {false !N} = Nat<! refl
<:!-refl {true  !N} = Nat<! refl
<:!-refl {false ! A ⇒ B} =
  Fun<! {q = false} refl <:!-refl (<:!-refl {A = B})
<:!-refl {true  ! A ⇒ B} =
  Fun<! {q = false} refl <:!-refl (<:!-refl {A = B})

-- interpret a Tp! as a Tp (Denotation)
infix 100 ⟦_⟧

⟦_⟧ : Tp! → Tp
⟦ false !N ⟧ = N
⟦ true  !N ⟧ = L N
⟦ false ! A ⇒ B ⟧ = ⟦ A ⟧ ⇒ ⟦ B ⟧
⟦ true  ! A ⇒ B ⟧ = L (⟦ A ⟧ ⇒ ⟦ B ⟧)

-- normalize a Tp as a Tp!
infix 100 ⌈_⌉

⌈_⌉ : Tp → Tp!
⌈ N ⌉       = false !N
⌈ L T ⌉     = ↑ ⌈ T ⌉
⌈ T ⇒ T' ⌉  = false ! ⌈ T ⌉ ⇒ ⌈ T' ⌉

-- Soundness

nat-sound : ∀ {b b' : Bool} →
            layerOK b b' ≡ true →
            ⟦ b !N ⟧ <: ⟦ b' !N ⟧
nat-sound {false} {false} refl = refl-raw
nat-sound {false} {true} refl = Pure
nat-sound {true} {true} refl = refl-raw
nat-sound {true} {false} ()

-- ⟦ ↑ A⟧ <: L ⟦ A ⟧
↑<L⟦⟧ : ∀ (A : Tp!) → ⟦ ↑ A ⟧ <: L ⟦ A ⟧
↑<L⟦⟧ (false !N) = refl-raw
↑<L⟦⟧ (true  !N) = Pure
↑<L⟦⟧ (false ! A ⇒ B) = refl-raw
↑<L⟦⟧ (true !  A ⇒ B) = Pure

-- L ⟦ A ⟧ <: ⟦ ↑ A ⟧
L⟦⟧<↑ : ∀ (A : Tp!) → L ⟦ A ⟧ <: ⟦ ↑ A ⟧
L⟦⟧<↑ (false !N) = refl-raw
L⟦⟧<↑ (true  !N) = Join
L⟦⟧<↑ (false ! A ⇒ B) = refl-raw
L⟦⟧<↑ (true  ! A ⇒ B) = Join

-- Soundness for ordinary function rule (not seq shaped)
funOrd-sound : ∀ {b b' : Bool} {A B A' B' : Tp!} →
               layerOK b b' ≡ true →
               ⟦ A' ⟧ <: ⟦ A ⟧ →
               ⟦ B  ⟧ <: ⟦ B' ⟧ →
               ⟦ b ! A ⇒ B ⟧ <: ⟦ b' ! A' ⇒ B' ⟧
funOrd-sound {false} {false} ok dom cod =
  Fun dom cod
funOrd-sound {false} {true} ok dom cod =
  Trans (Fun dom cod) Pure
funOrd-sound {true} {false} () dom cod
funOrd-sound {true} {true} ok dom cod =
  Cov (Fun dom cod)

-- Soundness for Seq-shaped function rule where b, b' = false
seq-core-sound : ∀ {A B A' B' : Tp!} →
                 ⟦ A' ⟧ <: ⟦ ↑ A ⟧ →
                 ⟦ ↑ B ⟧ <: ⟦ B' ⟧ →
                 L (⟦ A ⟧ ⇒ ⟦ B ⟧) <: ⟦ A' ⟧ ⇒ ⟦ B' ⟧
seq-core-sound {A} {B} dom cod =
  Trans Seq
    (Fun (Trans dom (↑<L⟦⟧ A))
         (Trans (L⟦⟧<↑ B) cod))

-- Soundness for the full Seq-shaped fun rule
funSeq-sound : ∀ {b b' : Bool} {A B A' B' : Tp!} →
               ⟦ A' ⟧ <: ⟦ ↑ A ⟧ →
               ⟦ ↑ B ⟧ <: ⟦ B' ⟧ →
               ⟦ b ! A ⇒ B ⟧ <: ⟦ b' ! A' ⇒ B' ⟧
funSeq-sound {false} {false} dom cod =
  Trans Pure (seq-core-sound dom cod)
funSeq-sound {false} {true} dom cod =
  Trans (Trans Pure (seq-core-sound dom cod)) Pure
funSeq-sound {true} {false} dom cod =
  seq-core-sound dom cod
funSeq-sound {true} {true} dom cod =
  Trans (seq-core-sound dom cod) Pure

-- Main soundness theorem
sound! : ∀ {A B : Tp!} → A <:! B → ⟦ A ⟧ <: ⟦ B ⟧
sound! (Nat<! ok) =
  nat-sound ok
sound! (Fun<! {q = false} ok dom cod) =
  funOrd-sound ok (sound! dom) (sound! cod)
sound! (Fun<! {q = true} ok dom cod) =
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
pure! {false !N} = Nat<! refl
pure! {true  !N} = Nat<! refl
pure! {false ! A ⇒ B} =
  Fun<! {q = false} refl <:!-refl <:!-refl
pure! {true ! A ⇒ B} =
  Fun<! {q = false} refl <:!-refl <:!-refl

-- completeness for join
join! : ∀ {A : Tp!} → ↑ (↑ A) <:! ↑ A
join! {false !N} = Nat<! refl
join! {true  !N} = Nat<! refl
join! {false ! A ⇒ B} =
  Fun<! {q = false} refl <:!-refl <:!-refl
join! {true ! A ⇒ B} =
  Fun<! {q = false} refl <:!-refl <:!-refl

-- completeness for cov
cov! : ∀ {A B : Tp!} → A <:! B → ↑ A <:! ↑ B
cov! (Nat<! ok) =
  Nat<! refl
cov! (Fun<! {q = true} ok dom cod) =
  Fun<! {q = true} refl dom cod
cov! (Fun<! {q = false} ok dom cod) =
  Fun<! {q = false} refl dom cod

-- completeness for Seq
seq! : ∀ {A B : Tp!} →
       (true ! A ⇒ B) <:! (false ! ↑ A ⇒ ↑ B)
seq! =
  Fun<! {q = true}
        refl
        <:!-refl
        <:!-refl

-- Completeness for Trans

layerOK-trans : ∀ (b₁ b₂ b₃ : Bool) →
                layerOK b₁ b₂ ≡ true →
                layerOK b₂ b₃ ≡ true →
                layerOK b₁ b₃ ≡ true
layerOK-trans false b₂    b₃    p q = refl
layerOK-trans true  false b₃    ()
layerOK-trans true  true  false p ()
layerOK-trans true  true  true  p q = refl

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
  (Fun<! {q = false}
         {b = b₁} {b' = b₂}
         {A = A₁} {B = B₁}
         {A' = A₂} {B' = B₂}
         ok₁ dom₁ cod₁)
  (Fun<! {q = false}
         {b = .b₂} {b' = b₃}
         {A = .A₂} {B = .B₂}
         {A' = A₃} {B' = B₃}
         ok₂ dom₂ cod₂) =
  Fun<! {q = false}
        {b = b₁} {b' = b₃}
        {A = A₁} {B = B₁}
        {A' = A₃} {B' = B₃}
        (layerOK-trans b₁ b₂ b₃ ok₁ ok₂)
        (trans! dom₂ dom₁)
        (trans! cod₁ cod₂)

-- Ordinary followed by Seq-shaped.
trans!
  (Fun<! {q = false} ok₁ dom₁ cod₁)
  (Fun<! {q = true} ok₂ dom₂ cod₂) =
  Fun<! {q = true}
    refl
    (trans! dom₂ ((cov! dom₁)))
    (trans! ((cov! cod₁)) cod₂)

-- Seq-shaped followed by ordinary.
trans!
  (Fun<! {q = true} ok₁ dom₁ cod₁)
  (Fun<! {q = false} ok₂ dom₂ cod₂) =
  Fun<! {q = true}
    refl
    (trans! dom₂ dom₁)
    (trans! cod₁ cod₂)

-- Seq-shaped followed by Seq-shaped.
trans!
  (Fun<! {q = true} ok₁ dom₁ cod₁)
  (Fun<! {q = true} ok₂ dom₂ cod₂) =
  Fun<! {q = true}
    refl
    (trans! dom₂ (trans! (cov! dom₁) join! ))
    (trans! (trans! cod₁ pure!) cod₂)


-- Full Completeness
complete! : ∀ {A B : Tp} → A <: B → ⌈ A ⌉ <:! ⌈ B ⌉
complete! NatRefl =
  Nat<! refl

complete! (Fun dom cod) =
  Fun<! {q = false} refl
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
