{-# OPTIONS --guardedness #-}

module Codata.M-type where

open import Data.Product

record M (A : Set) (B : A → Set) : Set where
  coinductive
  field
    shape : A
    pos : B shape → M A B
open M

unfold : ∀ {A B} {X : Set} 
  → (X → Σ[ a ∈ A ] (B a → X))
  → X → M A B
shape (unfold f x) = proj₁ (f x)
pos (unfold f x) b = unfold f (proj₂ (f x) b)
