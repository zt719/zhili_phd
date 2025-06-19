{-# OPTIONS --guardedness #-}

module Codata.M-type where

open import Data.Product

record M (A : Set) (B : A → Set) : Set where
  coinductive
  field
    out : Σ A (λ a → B a → M A B)
open M

m-iter : ∀ {A B} (S : Set)
  → (step : S → Σ A (λ a → B a → S))
  → S → M A B
out (m-iter S step s) with step s
... | (a , next) = a , λ b → m-iter S step (next b)

m-rec : ∀ {A B} (P : M A B → Set)
  → ((m : M A B) → P m → Σ A (λ a → Σ (B a → M A B) (λ f → (∀ b → P (f b)))))
  → (m : M A B) → P m
m-rec P step m = {!!}
-- ... | (a , f , p) = a , λ b → m-rec P step (f b)
