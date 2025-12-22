{-# OPTIONS --guardedness #-}

module Cont.Cont-munu where

open import Data.Empty
open import Data.Product
open import Function.Base

variable X Y : Set

Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

------------------------------------------------------

-- F : Set → Set
-- F X = X ⊎ μ F

data Tm : Set₁

record Cont : Set₁

data Tm where
  Πᵗ : (I : Set) (f : I → Tm) → Tm
  Σᵗ : (I : Set) (f : I → Tm) → Tm
  μ : (SP : Cont) → Tm
  ν : (SP : Cont) → Tm

record Cont where
  constructor _◃_+_+_
  field
    S : Set
    P : S → Set
    Pμ : S → Set
    Pν : S → Set

⟦_⟧ᵗ : Tm → Set → Set
⟦_⟧ᶜ : Cont → Set → Set
data W (SP : Cont) : Set
record M (SP : Cont) : Set

⟦ Πᵗ I f ⟧ᵗ X = Π I (λ i → ⟦ f i ⟧ᵗ X)
⟦ Σᵗ I f ⟧ᵗ X = Σ I (λ i → ⟦ f i ⟧ᵗ X)
⟦ μ SP ⟧ᵗ X = W SP
⟦ ν SP ⟧ᵗ X = M SP

⟦ S ◃ P + Pμ + Pν ⟧ᶜ X = Σ[ s ∈ S ] ((P s → X) × Pμ s × Pν s)

data W SP where
  sup : ⟦ SP ⟧ᶜ (W SP) → W SP

record M SP where
  coinductive
  field
    inf : ⟦ SP ⟧ᶜ (M SP)

module a where

  open Cont

  Πᶜ : (I : Set) → (I → Cont) → Cont
  Πᶜ I f = Π I (λ i → f i .S) ◃ (λ g → Σ[ i ∈ I ] f i .P (g i))
    + (λ g → Σ[ i ∈ I ] f i .Pμ (g i)) + (λ g → Σ[ i ∈ I ] f i .Pν (g i))

  Σᶜ : (I : Set) → (I → Cont) → Cont
  Σᶜ I f = Σ I (λ i → f i .S) ◃ (λ (i , s) → let (S ◃ P + Pμ + Pν) = f i in {!!}) + {!!} + {!!}

open a

nf : Tm → Cont
nf (Πᵗ I f) = Πᶜ I (nf ∘ f)
nf (Σᵗ I f) = Σᶜ I (nf ∘ f)
nf (μ SP) = {!!}
nf (ν SP) = {!!}
