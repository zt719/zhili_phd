open import Data.Product

module Cont.FF where

open import Cont.Cont

data F (X : Set) : Set where
  mkF : F (F X) → F X

-- ⟦ FS ◃ FP ⟧ X ≅ ⟦ FS ◃ FP ⟧ (⟦ FS ◃ FP ⟧ X)

-- (S ◃ P) ∘C (T ◃ Q) = (Σ[ s ∈ S ] (P s → T)) ◃ λ (s , f) → Σ[ p ∈ P s ] Q (f p)

-- FS ≅ Σ[ s ∈ FS ] FP s → FS
-- FP ≅ λ (s , f) → Σ[ p ∈ FP s ] FP (f p)

record FS : Set

record FP (sf : FS) : Set

record FS where
  inductive
  field
    s : FS
    f : FP s → FS

record FP sf where
  inductive
  open FS sf
  field
    p : FP s
    q : FP (f p)

FCont : Cont
FCont = FS ◃ FP
