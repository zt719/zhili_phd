{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude

data S¹ : Type where
  base : S¹
  loop : base ≡ base
  
record Cont : Type₁ where
  field
    S : Type
    P : S → Type
    E : (s : S) → P s → Σ[ s₁ ∈ S ] P s₁

record ⟦_⟧ (SP : Cont) (X : Type) : Type where
  open Cont SP
  field
    s : S
    f : P s → X
--    e : E s 
