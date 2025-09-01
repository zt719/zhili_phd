{-# OPTIONS --cubical --guardedness #-}
module Data.Pullback where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓ'' : Level

Pullback
  : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (f : A → C) (g : B → C) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
Pullback f g = Σ[ a ∈ _ ] Σ[ b ∈ _ ] (f a ≡ g b)
