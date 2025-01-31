{-# OPTIONS --cubical --without-K #-}

module STLC where

open import Cubical.Foundations.Prelude
  hiding (_,_; _∙_; I)

data UU : Set
data EL : UU → Set

data UU where
  con : UU
  ty  : UU
  tms : EL con → EL con → UU
  tm  : EL con → EL ty  → UU

Con : Set
Con = EL con

variable Γ Δ Θ Ξ : Con

Ty : Set
Ty = EL ty

variable A B C : Ty

Tms : Con → Con → Set
Tms Γ Δ = EL (tms Γ Δ)

variable σ δ ν : Tms Γ Δ

Tm : Con → Ty → Set
Tm Γ A = EL (tm Γ A)

variable t u : Tm Γ A

infixr 20 _⇒_
infixl 5 _▹_
infixl 5 _,_
infixr 9 _∘_

data EL where
  id   : Tms Γ Γ
  _∘_  : Tms Δ Θ → Tms Γ Δ → Tms Γ Θ

  ass  : (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
  idl  : id ∘ σ ≡ σ
  idr  : σ ∘ id ≡ σ

  _[_] : Tm Δ A → Tms Γ Δ → Tm Γ A

  ∙    : Con
  ε    : Tms Γ ∙
  ∙-η  : σ ≡ ε
  
  _▹_  : Con → Ty → Con
  _,_  : Tms Γ Δ → Tm Γ A → Tms Γ (Δ ▹ A)

  π₁   : Tms Γ (Δ ▹ A) → Tms Γ Δ
  π₂   : Tms Γ (Δ ▹ A) → Tm Γ A
  ▹-β₁ : π₁ (σ , t) ≡ σ
  ▹-β₂ : π₂ (σ , t) ≡ t
  ▹-η  : π₁ σ , π₂ σ ≡ σ
  
  ,-∘  : (σ , t) ∘ δ ≡ σ ∘ δ , t [ δ ]

  U : Ty
  _⇒_ : Ty → Ty → Ty
  
  ƛ   : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  ƛ⁻¹ : Tm Γ (A ⇒ B) → Tm (Γ ▹ A) B
  ⇒-β : ƛ⁻¹ (ƛ t) ≡ t
  ⇒-η : ƛ (ƛ⁻¹ t) ≡ t

-- _▹-map_ : Tms Γ Δ → (A : Ty) → Tms (Γ ▹ A) (Δ ▹ A)
-- ▹-map-≡ : σ ▹-map A ≡ σ ∘ (π₁ id) , π₂ id
-- ƛ-[]′ : {t : Tm (Γ ▹ A) B} → (ƛ t) [ σ ] ≡ ƛ (t [ σ ▹-map A ])

infix  1 begin_
begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

[id] : t [ id ] ≡ t
[id] {t = t} =
  begin
    t [ id ]
  ≡⟨ sym ▹-β₂ ⟩
    π₂ (id , t [ id ])
  ≡⟨ cong (λ x → π₂ (x , t [ id ])) (sym idl) ⟩
    π₂ (id ∘ id , t [ id ])
  ≡⟨ cong π₂ (sym ,-∘) ⟩
    π₂ ((id , t) ∘ id)
  ≡⟨ cong π₂ idr ⟩
    π₂ (id , t)
  ≡⟨ ▹-β₂ ⟩
    t
  ∎

[∘] : t [ σ ∘ δ ] ≡ t [ σ ] [ δ ]
[∘] {t = t} {σ = σ} {δ = δ} =
  begin
    t [ σ ∘ δ ]
  ≡⟨ sym ▹-β₂ ⟩
    π₂ (σ ∘ δ , t [ σ ∘ δ ])
  ≡⟨ cong (λ x → π₂ (x , t [ σ ∘ δ ])) (sym idl) ⟩
    π₂ (id ∘ σ ∘ δ , t [ σ ∘ δ ])
  ≡⟨ cong π₂ (sym ,-∘) ⟩
    π₂ ((id , t) ∘ σ ∘ δ)
  ≡⟨ cong π₂ (sym ass) ⟩
    π₂ (((id , t) ∘ σ) ∘ δ)
  ≡⟨ cong (λ x → π₂ (x ∘ δ)) ,-∘ ⟩
    π₂ ((id ∘ σ , t [ σ ]) ∘ δ)
  ≡⟨ cong π₂ ,-∘ ⟩
    π₂ ((id ∘ σ) ∘ δ , t [ σ ] [ δ ])
  ≡⟨ ▹-β₂ ⟩
    t [ σ ] [ δ ]
  ∎

wk : Tms (Γ ▹ A) Γ
wk = π₁ id

vz : Tm (Γ ▹ A) A
vz = π₂ id

vs : Tm Γ A → Tm (Γ ▹ B) A
vs t = t [ wk ]

<_> : Tm Γ A → Tms Γ (Γ ▹ A)
< t > = id , t

infixl 20 _$_
_$_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
t $ u = (ƛ⁻¹ t) [ < u > ]

I : Tm ∙ (A ⇒ A)
I = ƛ vz

S : Tm ∙ (A ⇒ B ⇒ A)
S = ƛ (ƛ (vs vz))

K : Tm ∙ ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
K = ƛ (ƛ (ƛ (vs (vs vz) $ vz $ (vs vz $ vz))))

_[_]¹ : Tm (Γ ▹ A) B → Tm Γ A → Tm Γ B
t [ u ]¹ = t [ < u > ]

_[_][_]² : Tm (Γ ▹ A ▹ B) C → Tm Γ A → Tm Γ B → Tm Γ C
t [ u ][ v ]² = t [ id , u , v ] 

β : ƛ t $ u ≡ t [ u ]¹
β {u = u} = cong _[ < u > ] ⇒-β

vz-[] : vz [ σ , u ] ≡ u
vz-[] {σ = σ} {u = u} =
    π₂ id [ σ , u ]
  ≡⟨ sym ▹-β₂ ⟩
    π₂ (π₁ id ∘ (σ , u) , π₂ id [ σ , u ])
  ≡⟨ cong π₂ (sym ,-∘) ⟩
    π₂ ((π₁ id , π₂ id) ∘ (σ , u))
  ≡⟨ cong (λ x → π₂ (x ∘ (σ , u))) ▹-η ⟩
    π₂ (id ∘ (σ , u))
  ≡⟨ cong π₂ idl ⟩
    π₂ (σ , u)
  ≡⟨ ▹-β₂ ⟩
    u
  ∎

vs-[] : vs t [ σ , u ] ≡ t [ σ ]
vs-[] {t = t} {σ = σ} {u = u} =
  begin
    t [ π₁ id ] [ σ , u ]
  ≡⟨ sym [∘] ⟩
    t [ π₁ id ∘ (σ , u) ]
  ≡⟨ cong (t [_]) (sym ▹-β₁) ⟩
    t [ π₁ (π₁ id ∘ (σ , u) , π₂ id [ σ , u ]) ]
  ≡⟨ cong (λ x → t [ π₁ x ]) (sym ,-∘) ⟩
    t [ π₁ ((π₁ id , π₂ id) ∘ (σ , u)) ]
  ≡⟨ cong (λ x → t [ π₁ (x ∘ (σ , u)) ]) ▹-η ⟩
    t [ π₁ (id ∘ (σ , u)) ]
  ≡⟨ cong (λ x → t [ π₁ x ]) idl ⟩
    t [ π₁ (σ , u) ]
  ≡⟨ cong (t [_]) ▹-β₁ ⟩
    t [ σ ]
  ∎

_↑ : Tms Γ Δ → Tms (Γ ▹ A) (Δ ▹ A)
σ ↑ = σ ∘ wk , vz

ƛ-[] : (ƛ t) [ σ ] ≡ ƛ (t [ σ ↑ ]) 
ƛ-[] {t = t} {σ = σ} = {!!}

ƛ⁻¹-[] : ƛ⁻¹ (t [ σ ]) ≡ ƛ⁻¹ t [ σ ↑ ]
ƛ⁻¹-[] {t = t} {σ = σ} =
  begin
    ƛ⁻¹ (t [ σ ])
  ≡⟨ cong (λ x → ƛ⁻¹ (x [ σ ])) (sym ⇒-η) ⟩
    ƛ⁻¹ (ƛ (ƛ⁻¹ t) [ σ ])
  ≡⟨ cong ƛ⁻¹ ƛ-[] ⟩
    ƛ⁻¹ (ƛ (ƛ⁻¹ t [ σ ↑ ]))
  ≡⟨ ⇒-β ⟩
    ƛ⁻¹ t [ σ ↑ ]
  ∎

ƛ-[]′ : (ƛ t) [ σ ] ≡ ƛ (t [ σ ↑ ]) 
ƛ-[]′ {t = t} {σ = σ} =
  begin
    ƛ t [ σ ]
  ≡⟨ sym ⇒-η ⟩
    ƛ (ƛ⁻¹ (ƛ t [ σ ]))
  ≡⟨ cong ƛ ƛ⁻¹-[] ⟩
    ƛ (ƛ⁻¹ (ƛ t) [ σ ↑ ])
  ≡⟨ cong (λ x → ƛ (x [ σ ↑ ])) ⇒-β ⟩
    ƛ (t [ σ ↑ ])
  ∎

-- ƛ⁻¹-[] : ƛ⁻¹ (t [ σ ]) ≡ ƛ⁻¹ t [ σ ↑ ]
--   ,-∘  : (σ , t) ∘ δ ≡ σ ∘ δ , t [ δ ]
η : ƛ (vs t $ vz) ≡ t
η {t = t} =
  begin
    ƛ (ƛ⁻¹ (t [ π₁ id ]) [ id , π₂ id ])
  ≡⟨ {!!} ⟩
    ƛ (ƛ⁻¹ t [ π₁ id ∘ id , π₂ id [ id ] ])
  ≡⟨ {!!} ⟩
    ƛ (ƛ⁻¹ t [ id ∘ π₁ id , π₂ id ])
  ≡⟨ refl ⟩
    ƛ (ƛ⁻¹ t [ id ↑ ])
  ≡⟨ {!!} ⟩
    ƛ (ƛ⁻¹ t [ id ])
  ≡⟨ cong ƛ [id] ⟩
    ƛ (ƛ⁻¹ t)
  ≡⟨ ⇒-η ⟩
    t
  ∎

-- t ⁺ [ u ]¹ ≡ t
-- ...
