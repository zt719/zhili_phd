{-# OPTIONS --guardedness #-}

module FF where

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat

-- F X ≃ 1 + X × F (F X)
-- ⟦ S ◃ P ⟧ X = ⟦ ⊤ ◃ ⊥ ⟧ X + ⟦ ⊤ ◃ ⊤ ⟧ X × ⟦ S ◃ P ⟧ (⟦ S ◃ P ⟧ X)

-- (⊤ ◃ ⊥) ⊎C (⊤ ◃ ⊤) ×C ((S ◃ P) ∘C (S ◃ P))
-- = (⊤ ◃ ⊥) ⊎C (⊤ ◃ ⊤) ×C ((Σ[ s ∈ S ] (P s → S)) ◃ (λ (s , f) → Σ[ p ∈ P s ] P (f p)))
-- = (⊤ ◃ ⊥) ⊎C (Σ[ s ∈ S ] (P s → S)) ◃ (λ (s , f) → ⊤ ⊎ Σ[ p ∈ P s ] P (f p))
-- = ⊤ ⊎ Σ[ s ∈ S ] (P s → S) ◃ λ{ inl tt → ⊥ ; inr (s , f) → ⊤ ⊎ Σ[ p ∈ P s ] P (f p) }

-- F X = 1 + X × F X

-- 2W : 2Cont → Cont
-- W : Cont → Set

case : {A B : Set} → (A → Set) → (B → Set) → A ⊎ B → Set
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

record νS : Set

record νP (s : νS) : Set
  
record νS where
  coinductive
  field
    outS : ⊤ ⊎ Σ[ s ∈ νS ] (νP s → νS)

record νP s where
  inductive
  open νS
  field
    outP : case (λ{ tt → ⊥ }) (λ{ (s , f) → ⊤ ⊎ Σ[ p ∈ νP s ] νP (f p) }) (outS s)

{-
record νS : Set

νP : νS → Set
  
record νS where
  coinductive
  field
    outS : ⊤ ⊎ Σ[ s ∈ νS ] (νP s → νS)

νP s with νS.outS s
... | inj₁ tt = ⊥
... | inj₂ (s , f) = ⊤ ⊎ Σ[ p ∈ νP s ] νP (f p)
-}

record μS : Set

record μP (s : μS) : Set

record μS where
  inductive
  field
    inμS : ⊤ ⊎ Σ[ s ∈ μS ] (μP s → μS)
  
record μP s where
  inductive
  open μS  
  field
    inμP : case (λ{ tt → ⊥ }) (λ{ (s , f) → ⊤ ⊎ Σ[ p ∈ μP s ] μP (f p) }) (inμS s)

-- H : (Set → Set) → Set → Set
-- H F X = 1 + X × F (F X)
