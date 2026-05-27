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
  true  !N   means L⁺ N  (represented canonically as L N)

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
  We assume A' <: A and B <: B', so we know F <: G.
  Therefore the outer flags must satify layerOK b b' to prevent L F <: G.

  If q = true, this is a Seq-shaped rule.
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
