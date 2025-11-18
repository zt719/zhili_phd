module CWF.new where

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

record SCwF : Set₁ where

  infixl 5 _▹_
  infixl 5 _,_
  infixr 9 _∘_
  
  field
  
    -- Con,Tms are a category
    Con : Set
    Tms : Con → Con → Set
    id  : {Γ : Con} → Tms Γ Γ
    _∘_ : {Γ Δ Θ : Con} → Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
    idl : {Γ Δ : Con} {γ : Tms Δ Γ} → id ∘ γ ≡ γ
    idr : {Γ Δ : Con} {γ : Tms Δ Γ} → γ ∘ id ≡ γ
    ass : {Γ Δ Θ Ξ : Con} {γ : Tms Δ Γ} {δ : Tms Θ Δ} {θ : Tms Ξ Θ}
          → (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)

    -- Tm _ A is a presheaf
    Ty : Set
    Tm : Con → Ty → Set    
    _[_] : {Γ Δ : Con} {A : Ty} → Tm Γ A → Tms Δ Γ → Tm Δ A
    [id] : {Γ : Con} {A : Ty} {t : Tm Γ A} → t [ id ] ≡ t
    [∘]  : {Γ Δ Θ : Con} {A : Ty} {t : Tm Γ A} {γ : Tms Δ Γ} {δ : Tms Θ Δ}
         → t [ γ ∘ δ ] ≡ t [ γ ] [ δ ]
    
    -- empty context
    • : Con
    ε : {Γ : Con} → Tms Γ •
    •-η : {Γ : Con}{γ : Tms Γ •} → γ ≡ ε
    
    -- context extension
    _▹_ : Con → Ty → Con
    _,_ : {Γ Δ : Con} {A : Ty} → Tms Δ Γ → Tm Δ A → Tms Δ (Γ ▹ A)
    π₁  : {Γ Δ : Con} {A : Ty} → Tms Γ (Δ ▹ A) → Tms Γ Δ
    π₂  : {Γ Δ : Con} {A : Ty} → Tms Γ (Δ ▹ A) → Tm Γ A
    π₁β : {Γ Δ : Con} {A : Ty} {γ : Tms Δ Γ} {t : Tm Δ A} → π₁ (γ , t) ≡ γ
    π₂β : {Γ Δ : Con} {A : Ty} {γ : Tms Δ Γ} {t : Tm Δ A} → π₂ (γ , t) ≡ t
    πη  : {Γ Δ : Con} {A : Ty} {γ : Tms Δ (Γ ▹ A)} → (π₁ γ , π₂ γ) ≡ γ
    ,∘  : {Γ Δ Θ : Con} {A : Ty} {γ : Tms Δ Γ} {δ : Tms Θ Δ} {t : Tm Δ A}
          → (γ , t) ∘ δ ≡ γ ∘ δ , t [ δ ]

  wk : {Γ : Con} {A : Ty} → Tms (Γ ▹ A) Γ
  wk = π₁ id

  vz : {Γ : Con} {A : Ty} → Tm (Γ ▹ A) A
  vz = π₂ id

  vs : {Γ : Con} {A B : Ty} → Tm Γ A → Tm (Γ ▹ B) A
  vs t = t [ wk ]

  <_> : {Γ : Con} {A : Ty} → Tm Γ A → Tms Γ (Γ ▹ A)
  < t > = id , t
