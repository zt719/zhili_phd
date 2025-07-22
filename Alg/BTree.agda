{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

variable
  X Y A : Set

data BTree (A : Set) : Set where
  leaf : BTree A
  node : BTree A → A → BTree A → BTree A

[l,n] : ⊤ ⊎ BTree A × A × BTree A → BTree A
[l,n] (inj₁ tt) = leaf
[l,n] (inj₂ (lt , a  , rt)) = node lt a lt

fold : (f : ⊤ ⊎ X × A × X → X)
  → BTree A → X
fold f leaf = f (inj₁ tt)
fold f (node lt a rt) = f (inj₂ (fold f lt , a , fold f rt))

record BTree∞ (A : Set) : Set where
  coinductive
  field
    branch∞ : ⊤ ⊎ BTree∞ A × A × BTree∞ A
open BTree∞

unfold : (f : X → ⊤ ⊎ X × A × X)
  → X → BTree∞ A
branch∞ (unfold f x) with f x
... | inj₁ tt = inj₁ tt
... | inj₂ (lx , a , rx) = inj₂ (unfold f lx , a , unfold f rx)
