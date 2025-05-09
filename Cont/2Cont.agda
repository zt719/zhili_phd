{-# OPTIONS --type-in-type #-}

module Cont.2Cont where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Function.Base

record 2Cont : Set
record 2ContHom (C D : 2Cont) : Set

{-# NO_POSITIVITY_CHECK #-}
record 2Cont where
  inductive
  field
    S : Set
    P₀ : S → Set
    R₀ : (s : S) → P₀ s → 2Cont
    P₁ : S → Set

record 2ContHom C D where
  inductive
  eta-equality
  open 2Cont
  field
    f : C .S → D .S
    g₀ : (s : C .S) → D .P₀ (f s) → C .P₀ s
    h₀ : (s : C .S) (p₀ : D .P₀ (f s)) → 2ContHom (C .R₀ s (g₀ s p₀)) (D .R₀ (f s) p₀) 
    g₁ : (s : C .S) → D .P₁ (f s) → C .P₁ s

module _ where
  open 2ContHom
  
  {-# TERMINATING #-}
  2ContHomComp : ∀ {C D E} → 2ContHom D E → 2ContHom C D → 2ContHom C E
  2ContHomComp δ γ .f = δ .f ∘ γ .f
  2ContHomComp δ γ .g₀ s = γ .g₀ s ∘ δ .g₀ (γ .f s)
  2ContHomComp δ γ .h₀ s p₀ = 2ContHomComp (δ .h₀ (γ .f s) p₀) (γ .h₀ s (δ .g₀ (γ .f s) p₀))
  2ContHomComp δ γ .g₁ s = γ .g₁ s ∘ δ .g₁ (γ .f s)

{-# NO_POSITIVITY_CHECK #-}
record ⟦_⟧ (C : 2Cont) (F : Set → Set) (X : Set) : Set where
  inductive
  eta-equality
  open 2Cont C
  field
    s : S
    k₀ : (p₀ : P₀ s) → F (⟦ R₀ s p₀ ⟧ F X)
    k₁ : P₁ s → X

open 2Cont
{-# TERMINATING #-}
⟦_⟧₁ : (C : 2Cont)
  → {F G : Set → Set} {F₁ : ∀ {X Y} → (X → Y) → F X → F Y} → (∀ X → F X → G X)
  → {X Y : Set} → (X → Y)
  → ⟦ C ⟧ F X → ⟦ C ⟧ G Y
⟦ C ⟧₁ {F} {G} {F₁} α {X} {Y} f record { s = s ; k₀ = k₀ ; k₁ = k₁ } = record
  { s = s
  ; k₀ = λ p₀ → α (⟦ C .R₀ s p₀ ⟧ G Y) (F₁ (⟦ C .R₀ s p₀ ⟧₁ {F₁ = F₁} α f) (k₀ p₀))
  ; k₁ = f ∘ k₁
  }

{-# TERMINATING #-}
⟦_⟧Hom : {C D : 2Cont} (δ : 2ContHom C D) →
  (F : Set → Set) (F₁ : ∀ {X Y} → (X → Y) → F X → F Y) (X : Set) → ⟦ C ⟧ F X → ⟦ D ⟧ F X
⟦ record { f = f ; g₀ = g₀ ; h₀ = h₀ ; g₁ = g₁ } ⟧Hom F F₁ X
  record { s = s ; k₀ = k₀ ; k₁ = k₁ } =
  record { s = f s ; k₀ = λ p₀ → F₁ (⟦ h₀ s p₀ ⟧Hom F F₁ X) (k₀ (g₀ s p₀)) ; k₁ = k₁ ∘ g₁ s }
