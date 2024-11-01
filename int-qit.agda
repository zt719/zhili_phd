{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

data ℤ : Set where
  zero : ℤ
  suc : ℤ → ℤ
  prd : ℤ → ℤ
  ps  : {x : ℤ} → prd (suc x) ≡ x
  sp  : {x : ℤ} → suc (prd x) ≡ x


