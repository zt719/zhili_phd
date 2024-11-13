{-# OPTIONS --guardedness --cubical #-}

module N-ary-Container where

open import Cubical.Foundations.Prelude using (PathP; _≡_; refl)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_)
open import Cubical.Data.Vec using (Vec)
open import Cubical.Codata.Stream using (Stream)
open Stream
open import Cubical.Data.Fin using (Fin; fzero; fsuc)

open import Function using (id; _∘_)

-- N-ary Container
record Contₙ {n : ℕ} : Set₁ where
  constructor _◃_
  field
    S : Set
    P : Fin n → S → Set

record _⇒ₙ_ {n : ℕ} (M N : Contₙ {n}) : Set where
  constructor _◃_
  open Contₙ M
  open Contₙ N renaming (S to T; P to Q)
  field
    u : S → T
    f : {i : Fin n} (s : S) → Q i (u s) → P i s

record ⟦_⟧ₙ {n : ℕ} (S◃P : Contₙ {n}) (X : Fin n → Set) : Set where
  constructor _,_
  open Contₙ S◃P
  field
    s : S
    p : {i : _} → P i s → X i

⟦_⟧ₙ₁ : {n : ℕ} (S◃P : Contₙ {n})
  → {X Y : Fin n → Set} (f : {i : _} → X i → Y i) 
  → ⟦ S◃P ⟧ₙ X → ⟦ S◃P ⟧ₙ Y
⟦ S ◃ P ⟧ₙ₁ f (s , g) = s , f ∘ g

⟦_⟧ₙ₂ : {n : ℕ} {S◃P T◃Q : Contₙ {n}} (u◃f : S◃P ⇒ₙ T◃Q)
  → (X : Fin n → Set) → ⟦ S◃P ⟧ₙ X → ⟦ T◃Q ⟧ₙ X
⟦ u ◃ f ⟧ₙ₂ X (s , h) = u s , h ∘ f s
