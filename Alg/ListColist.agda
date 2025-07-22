{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

variable
  X Y A : Set

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

fold : (f : ⊤ ⊎ A × X → X)
  → List A → X
fold f [] = f (inj₁ tt)
fold f (a ∷ as) = f (inj₂ (a , fold f as))

record Colist (A : Set) : Set where
  coinductive
  field
    out : ⊤ ⊎ A × Colist A
open Colist

unfold : (f : X → ⊤ ⊎ A × X)
  → X → ⊤ ⊎ A × Colist A
unfold f x with f x
... | inj₁ tt = inj₁ tt
... | inj₂ (a , x') = inj₂ (a , as)
  where
  as : Colist _
  out as = unfold f x'
