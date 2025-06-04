{-# OPTIONS --guardedness #-}

module Codata.Conat where

open import Data.Maybe
open import Data.Sum

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞
open ℕ∞

co-recℕ∞ : (W : Set)
  → (W → ℕ∞ ⊎ Maybe W)
  → W → ℕ∞
pred∞ (co-recℕ∞ W p x) with p x
... | inj₁ n = pred∞ n
... | inj₂ (just x) = just (co-recℕ∞ W p x)
... | inj₂ nothing = nothing

zero∞ : ℕ∞
pred∞ zero∞ = nothing

suc∞ : ℕ∞ → ℕ∞
pred∞ (suc∞ n) = just n

∞ : ℕ∞
pred∞ ∞ = just ∞

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m +∞ n) with pred∞ m
... | nothing = pred∞ n
... | just m' = just (m' +∞ n)

{-
_*∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m *∞ n) with pred∞ m
... | nothing = nothing
... | just m' = just (m' *∞ n) 
-}
