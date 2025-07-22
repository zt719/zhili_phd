{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

variable
  X Y N A B : Set

data NTree (N A B : Set) : Set where
  leaf : B → NTree N A B
  node : A → (N → NTree N A B) → NTree N A B

fold : (f : B ⊎ A × (N → X) → X)
  → NTree N A B → X
fold f (leaf b) = f (inj₁ b)
fold f (node a br) = f (inj₂ (a , fold f ∘ br))

record NTree∞ (N A B : Set) : Set where
  coinductive
  field
    branch∞ : B ⊎ A × (N → NTree∞ N A B)
open NTree∞

unfold : (f : X → B ⊎ A × (N → X))
  → X → NTree∞ N A B
branch∞ (unfold f x) with f x
... | inj₁ b = inj₁ b
... | inj₂ (a , br) = inj₂ (a , unfold f ∘ br)
