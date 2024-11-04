{-# OPTIONS --cubical --without-K #-}

open import Cubical.Foundations.Prelude
  hiding (_,_)

-- Szumi

data UU : Set
data EL : UU → Set

data UU where
  con : UU
  ty : UU
  tms : EL con → EL con → UU
  tm : EL con → EL ty → UU

Con : Set
Con = EL con

variable Γ Δ Θ Ξ : Con

Ty : Set
Ty = EL ty

variable A B : Ty

Tms : Con → Con → Set
Tms Γ Δ = EL (tms Γ Δ)

variable σ δ ν : Tms Γ Δ

Tm : Con → Ty → Set
Tm Γ A = EL (tm Γ A)

variable t u : Tm Γ A

infixr 5 _▹_
infixr 5 _,_
infixr 9 _∘_
data EL where
  id   : Tms Γ Γ
  _∘_  : Tms Δ Θ → Tms Γ Δ → Tms Γ Θ

  ass  : (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
  idl  : id ∘ σ ≡ σ
  idr  : σ ∘ id ≡ σ

  _[_]t : Tm Δ A → Tms Γ Δ → Tm Γ A

  ∙    : Con
  ε    : Tms Γ ∙
  ∙-η  : σ ≡ ε
  
  _▹_  : Con → Ty → Con
  _,_  : Tms Γ Δ → Tm Γ A → Tms Γ (Δ ▹ A)
  π₁   : Tms Γ (Δ ▹ A) → Tms Γ Δ
  π₂   : Tms Γ (Δ ▹ A) → Tm Γ A
  ▹-β₁ : π₁ (σ , t) ≡ σ
  ▹-β₂ : π₂ (σ , t) ≡ t

  ,-∘  : (σ , t) ∘ δ ≡ σ ∘ δ , t [ δ ]t

  U : Ty

  _⇒_ : Ty → Ty → Ty
  ƛ    : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  ƛ⁻¹  : Tm Γ (A ⇒ B) → Tm (Γ ▹ A) B

  _▹-map_ : Tms Γ Δ → (A : Ty) → Tms (Γ ▹ A) (Δ ▹ A)
  ▹-map-≡ : σ ▹-map A ≡ σ ∘ (π₁ id) , π₂ id
  
  ⇒-β : ƛ⁻¹ (ƛ t) ≡ t
  ⇒-η : ƛ (ƛ⁻¹ t) ≡ t
  ƛ-[] : (ƛ t) [ δ ]t ≡ ƛ (t [ σ ▹-map A ]t)
