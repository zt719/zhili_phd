{-# OPTIONS --cubical-compatible #-}

module Cont.Cont where

open import Function.Base

-- Container
infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

private variable SP TQ WR : Cont

-- Container Hom
record Cont[_,_] (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    u : S → T
    f : (s : S) → Q (u s) → P s

-- Container Extension Functor
record ⟦_⟧ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    p : P s → X

⟦_⟧₁ : (FC : Cont) → {X Y : Set} → (X → Y) → ⟦ FC ⟧ X → ⟦ FC ⟧ Y
⟦ FC ⟧₁ f sp = sp .⟦_⟧.s , (f ∘ sp .⟦_⟧.p)
{-# INLINE ⟦_⟧₁ #-}

⟦_⟧₂ : {SP TQ : Cont} (uf : Cont[ SP , TQ ])
  → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ f ◃ g ⟧₂ X (s , p) = f s , (p ∘ g s)

