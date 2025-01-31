{-# OPTIONS --guardedness --cubical #-}

module Cont-2 where

open import Function.Base
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Sets

∥_∥ : ∀ {ℓ} → hSet ℓ → Type ℓ
∥ A , _ ∥ = A

infix  0 _◁_
record Cont : Type₁ where
  constructor _◁_
  field
    S : hSet ℓ-zero
    P : ∥ S ∥ → hSet ℓ-zero

record Cont[_,_] (SP TQ : Cont) : Type where
  constructor _◁_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    u : ∥ S ∥ → ∥ T ∥
    f : (s : ∥ S ∥) → ∥ Q (u s) ∥ → ∥ P s ∥

variable SP TQ WR : Cont

idCont : Cont[ SP , SP ]
idCont = id ◁ λ _ → id

∘Cont : Cont[ SP , TQ ] → Cont[ TQ , WR ] → Cont[ SP , WR ]
∘Cont (u ◁ f) (v ◁ g)  = v ∘ u ◁ λ s → f s ∘ g (u s)

postulate
  Cont-isSetHom : {SP TQ : Cont} → isSet Cont[ SP , TQ ]
-- Cont-isSetHom {S ◁ P} {T ◁ Q} (u ◁ f) (v ◁ g) p q i j =


CONT : Category (ℓ-suc ℓ-zero) ℓ-zero
CONT = record
  { ob = Cont
  ; Hom[_,_] = Cont[_,_]
  ; id = idCont
  ; _⋆_ = ∘Cont
  ; ⋆IdL = λ f → refl
  ; ⋆IdR = λ f → refl
  ; ⋆Assoc = λ f g h → refl
  ; isSetHom = Cont-isSetHom
  }

record ⟦_⟧ {ℓ} (SP : Cont) (X : hSet ℓ) : Type ℓ where
  constructor _,_
  open Cont SP
  field
    s : ∥ S ∥
    p : ∥ P s ∥ → ∥ X ∥

{-
⟦_⟧₁ : (SP : Cont) {X Y : Type}
  → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ S ◁ P ⟧₁ f (s , g) = s , f ∘ g

⟦_⟧₂ : {SP TQ : Cont} → Cont[ SP , TQ ]
   → (X : Type) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ u ◁ f ⟧₂ _ (s , h) = u s , h ∘ f s
-}

C→F : Cont → Functor (SET ℓ-zero) (SET ℓ-zero)
C→F (S ◁ P) = record
  { F-ob = λ X → {!⟦ S ◁ P ⟧ X!} ; F-hom = {!!} ; F-id = {!!} ; F-seq = {!!} }


{-
CH→N : Cont[ SP , TQ ] → Nat (C→F SP) (C→F TQ)
CH→N (u ◁ f) = record
  { η = λ X (s , h) → u s , h ∘ f s
  ; nat = λ f → refl
  }

module _ {α : Nat (C→F SP) (C→F TQ)} where
  open Nat α
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)

  m : (s : ∥ S ∥ ) → ⟦ T ◁ Q ⟧ ∥ P s ∥
  m s = η ∥ P s ∥ (s , id)

  N→CH : Nat (C→F SP) (C→F TQ) → Cont[ SP , TQ ]
  N→CH α = s ∘ m ◁ p ∘ m
    where open ⟦_⟧

  uf : Cont[ SP , TQ ]
  uf = N→CH α

  path : CH→N uf ≡ α
  path i = record
    { η = λ X (s , f) → nat f i (s , id)
    ; nat = λ f → isSet {!!} {!!} {!!}
    }

  is-contr : {SP TQ : Cont} {α : Nat (C→F SP) (C→F TQ)}
    → {!!}
  is-contr = {!!}
-}
