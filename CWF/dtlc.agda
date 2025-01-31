{-# OPTIONS --cubical --without-K #-}

module DTLC where

open import Cubical.Foundations.Prelude
  hiding (_,_; _∙_; I)
open import Cubical.Data.Nat

-- heterogenous equality
{-
infix 2 _⊢_≡[_]≡_
data _⊢_≡[_]≡_ {X : Set}(F : X → Set) : {x y : X} → F x → x ≡ y → F y → Set where
  refl-h : {x : X}{z : F x} → F ⊢ z ≡[ refl ]≡ z
-}

data UU : Set
data EL : UU → Set

data UU where
  con : UU
  ty  : EL con → UU
  tms : EL con → EL con → UU
  tm  : (Γ : EL con) → EL (ty Γ)  → UU

Con : Set
Con = EL con

variable Γ Δ Θ Ξ : Con

Ty : Con → Set
Ty Γ = EL (ty Γ)

variable A B C : Ty Γ

Tms : Con → Con → Set
Tms Γ Δ = EL (tms Γ Δ)

variable σ δ ν : Tms Γ Δ

Tm : (Γ : Con) → Ty Γ → Set
Tm Γ A = EL (tm Γ A)

variable t u : Tm Γ A

infixr 20 _⇒_
infixl 5 _▹_
infixr 5 _,_
infixr 9 _∘_
data EL where
  id   : Tms Γ Γ
  _∘_  : Tms Δ Θ → Tms Γ Δ → Tms Γ Θ

  ass  : (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
  idl  : id ∘ σ ≡ σ
  idr  : σ ∘ id ≡ σ

  _[_]T : Ty Δ → Tms Γ Δ → Ty Γ
  [id]T : A [ id ]T ≡ A
  [∘]T  : A [ σ ∘ δ ]T ≡ A [ σ ]T [ δ ]T

  _[_]t : Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]T)

  ∙    : Con
  ε    : Tms Γ ∙
  ∙-η  : σ ≡ ε
  
  _▹_  : (Γ : Con) → Ty Γ → Con
  _,_  : (σ : Tms Γ Δ) → Tm Γ (A [ σ ]T) → Tms Γ (Δ ▹ A)

  π₁   : Tms Γ (Δ ▹ A) → Tms Γ Δ
  π₂   : (σ : Tms Γ (Δ ▹ A)) → Tm Γ (A [ π₁ σ ]T)
  ▹-β₁ : π₁ (σ , t) ≡ σ
  {-
  ▹-β₂ : ? ⊢ ? ≡[ ? ]≡ ?
  --(λ σ → Tm Γ (A [ σ ]T)) ⊢ π₂ (δ , t) ≡[ ▹-β₁ ]≡ t
  
  ,-∘  : (σ , t) ∘ δ ≡ σ ∘ δ , t [ δ ]t

  U : Ty
  _⇒_ : Ty → Ty → Ty
  
  ƛ    : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  ƛ⁻¹  : Tm Γ (A ⇒ B) → Tm (Γ ▹ A) B

  _▹-map_ : Tms Γ Δ → (A : Ty) → Tms (Γ ▹ A) (Δ ▹ A)
  ▹-map-≡ : σ ▹-map A ≡ σ ∘ (π₁ id) , π₂ id
  
  ⇒-β : {t : Tm (Γ ▹ A) B} → ƛ⁻¹ (ƛ t) ≡ t
  ⇒-η : {t : Tm Γ (A ⇒ B)} → ƛ (ƛ⁻¹ t) ≡ t

  ƛ-[]t : {t : Tm (Γ ▹ A) B} → (ƛ t) [ σ ]t ≡ ƛ (t [ σ ▹-map A ]t)


{-
infix  1 begin_
begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

[id]t : t [ id ]t ≡ t
[id]t {t = t} =
  begin
    t [ id ]t
  ≡⟨ sym ▹-β₂ ⟩
    π₂ (id , t [ id ]t)
  ≡⟨ cong (λ x → π₂ (x , t [ id ]t)) (sym idl) ⟩
    π₂ (id ∘ id , t [ id ]t)
  ≡⟨ cong π₂ (sym ,-∘) ⟩
    π₂ ((id , t) ∘ id)
  ≡⟨ cong π₂ idr ⟩
    π₂ (id , t)
  ≡⟨ ▹-β₂ ⟩
    t
  ∎

[∘]t : t [ σ ∘ δ ]t ≡ t [ σ ]t [ δ ]t
[∘]t {t = t} {σ = σ} {δ = δ} =
  begin
    t [ σ ∘ δ ]t
  ≡⟨ sym ▹-β₂ ⟩
    π₂ (σ ∘ δ , t [ σ ∘ δ ]t)
  ≡⟨ cong (λ x → π₂ (x , t [ σ ∘ δ ]t)) (sym idl) ⟩
    π₂ (id ∘ σ ∘ δ , t [ σ ∘ δ ]t)
  ≡⟨ cong π₂ (sym ,-∘) ⟩
    π₂ ((id , t) ∘ σ ∘ δ)
  ≡⟨ cong π₂ (sym ass) ⟩
    π₂ (((id , t) ∘ σ) ∘ δ)
  ≡⟨ cong (λ x → π₂ (x ∘ δ)) ,-∘ ⟩
    π₂ ((id ∘ σ , t [ σ ]t) ∘ δ)
  ≡⟨ cong π₂ ,-∘ ⟩
    π₂ ((id ∘ σ) ∘ δ , t [ σ ]t [ δ ]t)
  ≡⟨ ▹-β₂ ⟩
    t [ σ ]t [ δ ]t
  ∎

wk : Tms (Γ ▹ A) Γ
wk = π₁ id

vz : Tm (Γ ▹ A) A
vz = π₂ id

vs : Tm Γ A → Tm (Γ ▹ B) A
vs t = t [ wk ]t


<_> : Tm Γ A → Tms Γ (Γ ▹ A)
< t > = id , t

_↑ : Tms Γ Δ → Tms (Γ ▹ A) (Δ ▹ A)
σ ↑ = σ ∘ wk , vz

infixl 20 _$_
_$_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
t $ u = (ƛ⁻¹ t) [ < u > ]t

I : Tm ∙ (A ⇒ A)
I = ƛ vz

S : Tm ∙ (A ⇒ B ⇒ A)
S = ƛ (ƛ (vs vz))

K : Tm ∙ ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
K = ƛ (ƛ (ƛ (vs (vs vz) $ vz $ (vs vz $ vz))))

_[_]t¹ : Tm (Γ ▹ A) B → Tm Γ A → Tm Γ B
t [ u ]t¹ = t [ < u > ]t

β : ƛ t $ u ≡ t [ u ]t¹
β {u = u} = cong _[ < u > ]t ⇒-β

vz≡ : vz [ σ , u ]t ≡ u
vz≡ = {!!}

vs≡ : (vs t) [ σ , u ]t ≡ t [ σ ]t
vs≡ = {!!}

η : {t : Tm Γ (A ⇒ B)}
  → ƛ (vs t $ vz) ≡ t
η {t = t} =
  begin
    ƛ (vs t $ vz)
  ≡⟨ {!!} ⟩ {!!}


-- t ⁺ [ u ]t¹ ≡ t
-- ...



-}
-}
