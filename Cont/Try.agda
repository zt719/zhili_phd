{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude

data S¹ : Type where
  base : S¹
  loop : base ≡ base
  
record Cont : Type₁ where
  field
    S : Type
    P : S → Type
--    ES : S → Type

record ⟦_⟧ (SP : Cont) (X : Type) : Type where
  open Cont SP
  field
    s : S
    p : P s → X
