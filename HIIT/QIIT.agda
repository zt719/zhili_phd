{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude hiding (Σ)

data Con : Type

variable Γ Δ : Con

data Ty : Con → Type

variable A B : Ty Γ

data Con where
  ε   : Con
  _,_ : (Γ : Con) → Ty Γ → Con
-- eq  : ((Γ , A) , B) ≡ (Γ , Σ A B)  

data Ty where
  *  : Ty Γ
  Σ : (A : Ty Γ) → Ty Γ → Ty (Γ , A)
