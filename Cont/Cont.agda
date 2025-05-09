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
    k : P s → X

⟦_⟧₁ : (SP : Cont) {X Y : Set} → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ f sk = sk .s , (f ∘ sk .k)
  where open ⟦_⟧
{-# INLINE ⟦_⟧₁ #-}

⟦_⟧₁' : (SP : Cont) {X Y : Set} → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁' f (s , k) = s , (f ∘ k)

⟦_⟧Hom : {SP TQ : Cont} (fg : ContHom SP TQ)
  → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ f ◃ g ⟧Hom X (s , k) = f s , (k ∘ g s)
