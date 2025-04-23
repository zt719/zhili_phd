{-# OPTIONS --guardedness #-}

module Codata.Cofin where

open import Codata.Conat
open import Data.Maybe

{-
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)
-}

record Fin∞ (n : ℕ∞) : Set where
  coinductive
  field
    pred∞ : Maybe (Fin∞ {!!})

