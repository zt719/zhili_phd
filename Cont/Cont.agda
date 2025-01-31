{-# OPTIONS --cubical #-}

module Cont.Cont where

open import Function.Base
open import Cubical.Foundations.Prelude hiding (_◁_)

-- Functor & Natural Transformation

record Func : Type₁ where
  field
    F₀ : Type → Type
    F₁ : ∀ {X Y} → (X → Y) → F₀ X → F₀ Y
    F-id : ∀ {X} → F₁ {X} id ≡ id
    F-∘ : ∀ {X Y Z} (f : Y → Z) (g : X → Y)
        → F₁ (f ∘ g) ≡ F₁ f ∘ F₁ g

record Nat (F G : Func) : Type₁ where
  open Func F
  open Func G renaming (F₀ to G₀; F₁ to G₁)
  field
    η : ∀ X → F₀ X → G₀ X
    nat : ∀ {X Y} (f : X → Y) → G₁ f ∘ η X ≡ η Y ∘ F₁ f

postulate
  Nat≡ : {F G : Func} {α β : Nat F G}
    → Nat.η α ≡ Nat.η β → α ≡ β

-- Container
infix  0 _◃_
record Cont : Type₁ where
  constructor _◃_
  field
    S : Type
    P : S → Type

private variable SP TQ WR : Cont

-- Container Hom
record Cont[_,_] (SP TQ : Cont) : Type where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    u : S → T
    f : (s : S) → Q (u s) → P s

-- Container Extension Functor
record ⟦_⟧ (SP : Cont) (X : Type) : Type where
  constructor _,_
  open Cont SP
  field
    s : S
    p : P s → X

⟦_⟧₁ : (SP : Cont)
  → {X Y : Type} → (X → Y)
  → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ f (s , g) = s , f ∘ g

⟦_⟧₂ : {SP TQ : Cont} (uf : Cont[ SP , TQ ])
  → (X : Type) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ u ◃ f ⟧₂ X (s , h) = u s , h ∘ f s

C→F : Cont → Func
C→F SP = record
  { F₀ = ⟦ SP ⟧
  ; F₁ = ⟦ SP ⟧₁
  ; F-id = refl
  ; F-∘ = λ f g → refl
  }

CH→N : Cont[ SP , TQ ] → Nat (C→F SP) (C→F TQ)
CH→N uf = record
  { η = ⟦ uf ⟧₂
  ; nat = λ f → refl
  }

-- ⟦_⟧ is fully-faithfull
module _ {α : Nat (C→F SP) (C→F TQ)} where
  open Nat α
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  open ⟦_⟧

  N→CH : Nat (C→F SP) (C→F TQ) → Cont[ SP , TQ ]
  N→CH α = s ∘ m ◃ p ∘ m
    where
      m : (s : S) → ⟦ T ◃ Q ⟧ (P s)
      m s = η (P s) (s , id)

  uf′ : Cont[ SP , TQ ]
  uf′ = N→CH α

  path : CH→N uf′ ≡ α
  path = Nat≡ (λ i X (s , f) → nat f i (s , id))

_∘c_ : Cont → Cont → Cont
(S ◃ P) ∘c (T ◃ Q) =
  Σ[ s ∈ S ] (P s → T) ◃ λ{ (s , f) → Σ[ p ∈ P s ] Q (f p) }
