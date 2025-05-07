{-# OPTIONS --cubical-compatible #-}

module Cont.Cont where

open import Function.Base

{- Container -}
infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

private variable SP TQ WR : Cont

{- Container Hom -}
record ContHom (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    f : S → T
    g : (s : S) → Q (f s) → P s

{- Container Extension Functor -}
record ⟦_⟧ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    p : P s → X

⟦_⟧₁ : (SP : Cont) {X Y : Set} → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ f sp = sp .⟦_⟧.s , (f ∘ sp .⟦_⟧.p)
{-# INLINE ⟦_⟧₁ #-}

⟦_⟧Hom : {SP TQ : Cont} (fg : ContHom SP TQ)
  → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ f ◃ g ⟧Hom X (s , p) = f s , (p ∘ g s)
