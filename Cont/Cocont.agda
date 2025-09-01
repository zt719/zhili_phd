{-# OPTIONS --guardedness #-}

module Cont.Cocont where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum

variable X Y : Set

-- F : Set → Set
-- F X = (X ⊎ ⊤) × X

record F (X : Set) : Set where
  coinductive
  field
    f₀ : X ⊎ ⊤
    f₁ : X
open F    

record BT∞ (X : Set) : Set where
  coinductive
  field
    v : X
    lt : BT∞ X
    rt : BT∞ X
open BT∞    

--G : Set → Set
--G X = (X × X) ⊎ X

data G (X : Set) : Set where
  g₀ : X → X → G X
  g₁ : X → G X

record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

⟦_⟧ : (SP : Cont) (X : Set) → Set
⟦ S ◃ P ⟧ X = (s : S) → Σ[ p ∈ P s ] X

⟦_⟧₁ : (SP : Cont) → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ f g s = g s .proj₁ , f (g s .proj₂)

-- s : S
-- x : (s : S) → Σ[ p ∈ P s ] X
-- f : X → Y

haha : BT∞ X → F X
f₀ (haha x) = inj₁ (v x)
f₁ (haha x) = x .v
