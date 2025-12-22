module Cont.ContTm where

open import Data.Empty
open import Data.Product
open import Function.Base

variable X Y : Set

Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

data Tm : Set₁ where
  Πᵗ : (I : Set) (f : I → Tm) → Tm
  Σᵗ : (I : Set) (f : I → Tm) → Tm

⊤ᵗ : Tm
⊤ᵗ = Πᵗ ⊥ λ ()

⊥ᵗ : Tm
⊥ᵗ = Σᵗ ⊥ λ ()

⟦_⟧Tm : Tm → Set → Set
⟦ Πᵗ I f ⟧Tm X = Π I (λ i → ⟦ f i ⟧Tm X)
⟦ Σᵗ I f ⟧Tm X = Σ I (λ i → ⟦ f i ⟧Tm X)

⟦_⟧Tm₁ : (t : Tm) → (X → Y) → ⟦ t ⟧Tm X → ⟦ t ⟧Tm Y
⟦ Πᵗ I f ⟧Tm₁ g h i = ⟦ f i ⟧Tm₁ g (h i)
⟦ Σᵗ I f ⟧Tm₁ g (i , h) = i , ⟦ f i ⟧Tm₁ g h

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set
    
record ⟦_⟧ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    f : (p : P s) → X

⟦_⟧₁ : (SP : Cont) → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g (s , f) = s , g ∘ f

Πᶜ : (I : Set) (f : I → Cont) → Cont
Πᶜ I f = ((i : I) → f i .Cont.S)
  ◃ λ g → Σ[ i ∈ I ] f i .Cont.P (g i)

Σᶜ : (I : Set) (f : I → Cont) → Cont
Σᶜ I f = (Σ[ i ∈ I ] f i .Cont.S)
  ◃ λ (i , s) → f i .Cont.P s

nf : Tm → Cont
nf (Πᵗ I f) = Πᶜ I (nf ∘ f)
nf (Σᵗ I f) = Σᶜ I (nf ∘ f)

emb : Cont → Tm
emb (S ◃ P) = Σᵗ S (λ s → Πᵗ (P s) (λ p → ⊤ᵗ))
