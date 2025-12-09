module Cont.ContTm where

open import Data.Empty
open import Data.Product
open import Function.Base

variable X Y : Set

Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

data Poly : Set₁ where
  Πᵗ : (I : Set) (f : I → Poly) → Poly
  Σᵗ : (I : Set) (f : I → Poly) → Poly

⊤ᵗ : Poly
⊤ᵗ = Πᵗ ⊥ λ ()

⊥ᵗ : Poly
⊥ᵗ = Σᵗ ⊥ λ ()

⟦_⟧Poly : Poly → Set → Set
⟦ Πᵗ I f ⟧Poly X = Π I (λ i → ⟦ f i ⟧Poly X)
⟦ Σᵗ I f ⟧Poly X = Σ I (λ i → ⟦ f i ⟧Poly X)

⟦_⟧Poly₁ : (t : Poly) → (X → Y) → ⟦ t ⟧Poly X → ⟦ t ⟧Poly Y
⟦ Πᵗ I f ⟧Poly₁ g h i = ⟦ f i ⟧Poly₁ g (h i)
⟦ Σᵗ I f ⟧Poly₁ g (i , h) = i , ⟦ f i ⟧Poly₁ g h

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

{-
record ⟦_⟧ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    f : (p : P s) → X
-}

⟦_⟧ : Cont → Set → Set
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : (SP : Cont) → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g (s , f) = s , g ∘ f

Πᶜ : (I : Set) (f : I → Cont) → Cont
Πᶜ I fs = ((i : I) → fs i .Cont.S)
  ◃ λ f → Σ[ i ∈ I ] fs i .Cont.P (f i)

Σᶜ : (I : Set) (f : I → Cont) → Cont
Σᶜ I fs = (Σ[ i ∈ I ] fs i .Cont.S)
  ◃ λ (i , s) → fs i .Cont.P s

nf : Poly → Cont
nf (Πᵗ I f) = Πᶜ I (nf ∘ f)
nf (Σᵗ I f) = Σᶜ I (nf ∘ f)

emb : Cont → Poly
emb (S ◃ P) = Σᵗ S (λ s → Πᵗ (P s) (λ p → ⊤ᵗ))

open import Relation.Binary.PropositionalEquality

Cont≡ : {S T : Set} (p : S ≡ T)
  → {P : S → Set} {Q : T → Set}
  → (P ≡ λ s → Q (subst (λ S → S) p s))
  → (S ◃ P) ≡ (T ◃ Q)
Cont≡ refl refl = refl

φ : (X : Set) (SP : Cont) → ⟦ emb SP ⟧Poly X ≡ ⟦ SP ⟧ X
φ X (S ◃ P) = {!!}
