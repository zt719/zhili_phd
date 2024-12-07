{-# OPTIONS --guardedness --cubical #-}

module NCont where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.Fin

record Cont {n : ℕ} : Set₁ where
  constructor _◃_
  field
    S : Set
    P : Fin n → S → Set

record _⇒_ {n : ℕ} (M N : Cont {n}) : Set where
  constructor _◃_
  open Cont M
  open Cont N renaming (S to T; P to Q)
  field
    u : S → T
    f : {i : Fin n} (s : S) → Q i (u s) → P i s

record ⟦_⟧ {n : ℕ} (S◃P : Cont {n}) (X : Fin n → Set) : Set where
  constructor _,_
  open Cont S◃P
  field
    s : S
    p : {i : _} → P i s → X i

⟦_⟧₁ : {n : ℕ} (S◃P : Cont {n})
  → {X Y : Fin n → Set} (f : {i : _} → X i → Y i) 
  → ⟦ S◃P ⟧ X → ⟦ S◃P ⟧ Y
⟦ S ◃ P ⟧₁ f (s , g) = s , f ∘ g

⟦_⟧₂ : {n : ℕ} {S◃P T◃Q : Cont {n}} (u◃f : S◃P ⇒ T◃Q)
  → (X : Fin n → Set) → ⟦ S◃P ⟧ X → ⟦ T◃Q ⟧ X
⟦ u ◃ f ⟧₂ X (s , h) = u s , h ∘ f s
