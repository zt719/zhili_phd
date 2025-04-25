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

⟦_⟧₁ : (SP : Cont) → {X Y : Set} → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ f sp = sp .⟦_⟧.s , (f ∘ sp .⟦_⟧.p)
{-# INLINE ⟦_⟧₁ #-}

⟦_⟧₂ : {SP TQ : Cont} (uf : ContHom SP TQ)
  → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ f ◃ g ⟧₂ X (s , p) = f s , (p ∘ g s)

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum

𝟘 : Cont
𝟘 = ⊥ ◃ λ ()

𝟙 : Cont
𝟙 = ⊤ ◃ λ{ tt → ⊥ }

Prod : Cont → Cont → Cont
Prod (S ◃ P) (T ◃ Q) = S × T ◃ λ{ (s , t) → P s ⊎ Q t }

Sum : Cont → Cont → Cont
Sum (S ◃ P) (T ◃ Q) = S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t }

-- Comp : Cont → Cont → Cont
-- Comp (S ◃ P) (T ◃ Q) = {!!}
