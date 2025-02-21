{-# OPTIONS --guardedness --cubical #-}

module 2Cont where

open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_)

record Cont₂ : Set₁ where
  inductive
  field
    S : Set
    P-F : S → Set
    P-A : S → Set
    R-F : (s : S) → P-F s → Cont₂

{-# NO_POSITIVITY_CHECK #-}
record ⟦_⟧ (cont : Cont₂) (F : Set → Set) (A : Set) : Set where
  inductive
  open Cont₂ cont
  field
    s : S
    p-f : (p : P-F s) → F (⟦ R-F s p ⟧ F A)
    p-a : P-A s → A

H : (Set → Set) → Set → Set
H F A = A × F (F A)

H′′-Cont : Cont₂
Cont₂.S H′′-Cont = ⊤
Cont₂.P-F H′′-Cont = λ x → ⊥
Cont₂.P-A H′′-Cont = λ x → ⊤
Cont₂.R-F H′′-Cont = λ s ()

H′-Cont : Cont₂
Cont₂.S H′-Cont = ⊤
Cont₂.P-F H′-Cont = λ x → ⊤
Cont₂.P-A H′-Cont = λ x → ⊥
Cont₂.R-F H′-Cont = λ s p → H′′-Cont

H-Cont : Cont₂
Cont₂.S H-Cont = ⊤
Cont₂.P-F H-Cont = λ x → ⊤
Cont₂.P-A H-Cont = λ x → ⊤
Cont₂.R-F H-Cont = λ s p → H′-Cont

H′ : (Set → Set) → Set → Set
H′ = ⟦ H-Cont ⟧
