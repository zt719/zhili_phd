module QIIT-Simple where

open import Relation.Binary.PropositionalEquality
  hiding ([_])
open ≡-Reasoning

data Con : Set
data Ty : Set
data Tms : Con → Con → Set
data Tm : Con → Ty → Set

data Con where
  ∙    : Con
  _▹_  : Con → Ty → Con

data Ty where

infixr 5 _,_
infixr 9 _∘_
data Tms where
  ε    : {Γ : Con} → Tms Γ ∙
  _,_  : {Γ Δ : Con} {A : Ty} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ ▹ A)
  id   : {Γ : Con} → Tms Γ Γ
  _∘_  : {Γ Δ Θ : Con} → Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
  π₁   : {Γ Δ : Con} {A : Ty} → Tms Γ (Δ ▹ A) → Tms Γ Δ

data Tm where 
  _[_]t : {Γ Δ : Con} {A : Ty} → Tm Δ A → Tms Γ Δ → Tm Γ A
  π₂   : {Γ Δ : Con} {A : Ty} → Tms Γ (Δ ▹ A) → Tm Γ A

postulate
  ass  : {Γ Δ Θ Ξ : Con} {σ : Tms Θ Ξ} {δ : Tms Δ Θ} {ν : Tms Γ Δ} → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
  idl  : {Γ Δ : Con} {σ : Tms Γ Δ} → id ∘ σ ≡ σ
  idr  : {Γ Δ : Con} {σ : Tms Γ Δ} → σ ∘ id ≡ σ
  ∙-η  : {Γ : Con} {σ : Tms Γ ∙} → σ ≡ ε
  ▹-β₁ : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {t : Tm Γ A} → π₁ (σ , t) ≡ σ
  ▹-β₂ : {Γ Δ : Con} {A : Ty} {σ : Tms Γ Δ} {t : Tm Γ A} → π₂ (σ , t) ≡ t
  ▹-η  : {Γ Δ : Con} {A : Ty} {σ : Tms Γ (Δ ▹ A)} → (π₁ σ , π₂ σ) ≡ σ
  ,-∘  : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {δ : Tms Γ Δ} {t : Tm Δ A} → (σ , t) ∘ δ ≡ σ ∘ δ , t [ δ ]t

[id]t : {Γ : Con} {A : Ty} {t : Tm Γ A} → t [ id ]t ≡ t
[id]t {t = t} =
  begin
    t [ id ]t
  ≡⟨ sym ▹-β₂ ⟩
    π₂ (id , (t [ id ]t))
  ≡⟨ cong (λ id′ → π₂ (id′ , (t [ id ]t))) (sym idl) ⟩
    π₂ (id ∘ id , (t [ id ]t))
  ≡⟨ cong π₂ (sym ,-∘) ⟩
    π₂ ((id , t) ∘ id)
  ≡⟨ cong π₂ idr ⟩
    π₂ (id , t)
  ≡⟨ ▹-β₂ ⟩
    t
  ∎

[∘]t : {Γ Δ Θ : Con} {A : Ty} {σ : Tms Δ Θ} {δ : Tms Γ Δ} {t : Tm Θ A}
  → t [ σ ∘ δ ]t ≡ t [ σ ]t [ δ ]t
[∘]t {σ = σ} {δ} {t} =
  begin
    t [ σ ∘ δ ]t
  ≡⟨ sym ▹-β₂ ⟩
    π₂ (σ ∘ δ , t [ σ ∘ δ ]t)
  ≡⟨ cong (λ σ∘δ → π₂ (σ∘δ , t [ σ ∘ δ ]t)) (sym idl) ⟩
    π₂ (id ∘ σ ∘ δ , t [ σ ∘ δ ]t)
  ≡⟨ cong π₂ (sym ,-∘) ⟩
    π₂ ((id , t) ∘ σ ∘ δ)
  ≡⟨ cong π₂ (sym ass) ⟩
    π₂ (((id , t) ∘ σ) ∘ δ)
  ≡⟨ cong (λ id,t∘σ → π₂ (id,t∘σ ∘ δ)) ,-∘ ⟩
    π₂ ((id ∘ σ , t [ σ ]t) ∘ δ)
  ≡⟨ cong π₂ ,-∘ ⟩
    π₂ (((id ∘ σ) ∘ δ , t [ σ ]t [ δ ]t))
  ≡⟨ ▹-β₂ ⟩
    t [ σ ]t [ δ ]t
  ∎ 

wk : {Γ : Con} {A : Ty} → Tms (Γ ▹ A) Γ
wk = π₁ id

vz : {Γ : Con} {A : Ty} → Tm (Γ ▹ A) A
vz = π₂ id

vs : {Γ : Con} {A B : Ty} → Tm Γ A → Tm (Γ ▹ B) A
vs t = t [ wk ]t

{-
C : Category
C = Con , Tms , id , _∘_ , idl , idr , ass

1 : Terminal Category
1 = ∙ , ε , ∙-η

TY : Functor (CON op) SET
TY = Ty , _[_]T , [id]T , [∘]T

TM : Functor ((∫ TY) op) SET
TM = Tm , _[_]t , [id]t , [∘]t
-}
