{-# OPTIONS --guardedness #-}

module NatConat where

open import Data.Unit
open import Data.Sum
open import Data.Product

open import Relation.Binary.PropositionalEquality

variable
  X Y : Set

{- X → ⊤ ⊎ X -}

⊤⊎₁ : (X → Y)
  → ⊤ ⊎ X → ⊤ ⊎ Y
⊤⊎₁ f (inj₁ tt) = inj₁ tt
⊤⊎₁ f (inj₂ x) = inj₂ (f x)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

[z,s] : ⊤ ⊎ ℕ → ℕ
[z,s] (inj₁ tt) = zero
[z,s] (inj₂ n) = suc n

fold : (f : ⊤ ⊎ X → X)
  → ℕ → X
fold f zero = f (inj₁ tt)
fold f (suc n) = f (inj₂ (fold f n))

commute : (x : ⊤ ⊎ ℕ) (f : ⊤ ⊎ X → X)
  → fold f ([z,s] x) ≡ f (⊤⊎₁ (fold f) x)
commute (inj₁ tt) f = refl
commute (inj₂ n) f = refl

[z,s]⁻ : ℕ → ⊤ ⊎ ℕ
[z,s]⁻ = fold (⊤⊎₁ [z,s])

φ : (n : ℕ)
  → [z,s] ([z,s]⁻ n) ≡ n
φ zero = refl
φ (suc n) = cong suc (φ n)

ψ : (x : ⊤ ⊎ ℕ)
  → [z,s]⁻ ([z,s] x) ≡ x
ψ (inj₁ tt) = refl
ψ (inj₂ n) = cong inj₂ (φ n)

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : ⊤ ⊎ ℕ∞
open ℕ∞ public

unfold : (f : X → ⊤ ⊎ X)
  → X → ℕ∞
pred∞ (unfold f x) with f x
... | inj₁ tt = inj₁ tt
... | inj₂ x = inj₂ (unfold f x)

one∞ : ℕ∞
pred∞ one∞ = inj₁ tt

∞ : ℕ∞
pred∞ ∞ = inj₂ ∞
