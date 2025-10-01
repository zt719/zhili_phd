What is a simply typed CWF?

```
module CWF.cwf-simple where

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
    id : {Γ : Con} → Tms Γ Γ
    _∘_ : {Γ Δ Θ : Con} → Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
    idl : {Γ Δ : Con} {γ : Tms Δ Γ} → id ∘ γ ≡ γ
    idr : {Γ Δ : Con} {γ : Tms Δ Γ} → γ ∘ id ≡ γ
    ass : {Γ Δ Θ Ξ : Con} {γ : Tms Δ Γ} {δ : Tms Θ Δ} {θ : Tms Ξ Θ}
          → (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)

    -- Tm _ A is a presheaf
    Ty : Set
    Tm : Con → Ty → Set    
    _[_] : ∀ {Γ Δ A} → Tm Γ A → Tms Δ Γ → Tm Δ A
    
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
          
  [id] : {Γ : Con} {A : Ty} {t : Tm Γ A} → t [ id ] ≡ t
  [id] {t = t} = 
    begin
    t [ id ]                 ≡⟨ sym π₂β ⟩
    π₂ (id , t [ id ])       ≡⟨ cong (λ x → π₂ (x , t [ id ])) (sym idl) ⟩
    π₂ (id ∘ id , t [ id ])  ≡⟨ cong π₂ (sym ,∘) ⟩
    π₂ ((id , t) ∘ id)       ≡⟨ cong π₂ idr ⟩
    π₂ (id , t)              ≡⟨ π₂β ⟩
    t                        ∎

  [∘] : {Γ Δ Θ : Con} {A : Ty} {t : Tm Γ A} {γ : Tms Δ Γ} {δ : Tms Θ Δ}
    → t [ γ ∘ δ ] ≡ t [ γ ] [ δ ]
  [∘] {t = t} {γ = γ} {δ = δ} =
    t [ γ ∘ δ ]                        ≡⟨ sym π₂β ⟩
    π₂ (γ ∘ δ , t [ γ ∘ δ ])           ≡⟨ cong (λ x → π₂ (x , t [ γ ∘ δ ])) (sym idl) ⟩
    π₂ (id ∘ γ ∘ δ , t [ γ ∘ δ ])      ≡⟨ cong π₂ (sym ,∘) ⟩
    π₂ ((id , t) ∘ γ ∘ δ)              ≡⟨ cong π₂ (sym ass) ⟩
    π₂ (((id , t) ∘ γ) ∘ δ)            ≡⟨ cong (λ x → π₂ (x ∘ δ)) ,∘ ⟩
    π₂ ((id ∘ γ , t [ γ ]) ∘ δ)        ≡⟨ cong π₂ ,∘ ⟩
    π₂ ((id ∘ γ) ∘ δ , t [ γ ] [ δ ])  ≡⟨ π₂β ⟩
    t [ γ ] [ δ ]                      ∎

  wk : {Γ : Con} {A : Ty} → Tms (Γ ▹ A) Γ
  wk = π₁ id

  vz : {Γ : Con} {A : Ty} → Tm (Γ ▹ A) A
  vz = π₂ id

  vs : {Γ : Con} {A B : Ty} → Tm Γ A → Tm (Γ ▹ B) A
  vs t = t [ wk ]

  <_> : {Γ : Con} {A : Ty} → Tm Γ A → Tms Γ (Γ ▹ A)
  < t > = id , t
```

Semantics
```
open import Data.Unit
open import Data.Product

data U : Set where
  ⊤U : U
  _×U_ : U → U → U 

El : U → Set
El ⊤U = ⊤
El (A ×U B) = El A × El B

open SCwF

model : SCwF
Con model = U
Ty model = U
Tm model Γ A = El Γ → El A
Tms model Γ Δ = El Γ → El Δ
id model x = x
_∘_ model f g x = f (g x)
idl model = refl
idr model = refl
ass model = refl
_[_] model f g x = f (g x)
-- [id] model = refl
-- [∘] model = refl
• model = ⊤U
ε model = λ x → tt
•-η model = refl
_▹_ model A B = A ×U B
SCwF._,_ model f g x = (f x) Data.Product., (g x)
π₁ model f x = proj₁ (f x)
π₂ model f x = proj₂ (f x)
π₁β model = refl
π₂β model = refl
πη model = refl
,∘ model = refl
-- π₁∘ model = refl
-- π₂∘ model = refl
```
