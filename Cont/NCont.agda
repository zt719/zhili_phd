module NCont where

open import Data.Nat
open import Data.Fin

open import Function.Base

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

record ⟦_⟧ {n : ℕ} (SP : Cont {n}) (X : Fin n → Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    p : {i : _} → P i s → X i

⟦_⟧₁ : {n : ℕ} (SP : Cont {n})
  → {X Y : Fin n → Set} (f : {i : _} → X i → Y i) 
  → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ S ◃ P ⟧₁ f (s , g) = s , (f ∘ g)

⟦_⟧₂ : {n : ℕ} {SP TQ : Cont {n}} (u◃f : SP ⇒ TQ)
  → (X : Fin n → Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ u ◃ f ⟧₂ X (s , h) = u s , (h ∘ f s)
