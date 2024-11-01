module QIIT-Dep where

open import Relation.Binary.PropositionalEquality
  hiding ([_])
open ≡-Reasoning

infix  2 _⊢_≡[_]≡_
data _⊢_≡[_]≡_ {X : Set} (F : X → Set) : {x y : X} → F x → x ≡ y → F y → Set where
  refl : {x : X} {z : F x} → F ⊢ z ≡[ refl ]≡ z

sym′ : {X : Set} {F : X → Set} {x y : X} {p : x ≡ y} {a : F x} {b : F y}
  → F ⊢ a ≡[ p ]≡ b
  → F ⊢ b ≡[ sym p ]≡ a
sym′ refl = refl

trans′ : {X : Set} {F : X → Set} {x y z : X} {p : x ≡ y} {q : y ≡ z} {a : F x} {b : F y} {c : F z}
  → F ⊢ a ≡[ p ]≡ b
  → F ⊢ b ≡[ q ]≡ c
  → F ⊢ a ≡[ trans p q ]≡ c
trans′ refl refl = refl

data Con : Set
data Ty  : Con → Set
data Tms : Con → Con → Set
data Tm  : (Γ : Con) → Ty Γ → Set

infixr 5 _▹_
data Con where
  ∙   : Con
  _▹_ : (Γ : Con) → Ty Γ → Con

data Ty where
  _[_]T : {Γ Δ : Con} → Ty Δ → Tms Γ Δ → Ty Γ

infixr 5 _,_
data Tms where
  ε   : {Γ : Con} → Tms Γ ∙
  _,_ : {Γ Δ : Con} {A : Ty Δ} → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]T) → Tms Γ (Δ ▹ A)
  id  : {Γ : Con} → Tms Γ Γ
  _∘_ : {Γ Δ Θ : Con} → Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
  π₁  : {Γ Δ : Con} {A : Ty Δ} → Tms Γ (Δ ▹ A) → Tms Γ Δ

data Tm where 
  _[_]t : {Γ Δ : Con} {A : Ty Δ} → Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]T)
  π₂    : {Γ Δ : Con} {A : Ty Δ} → (σ : Tms Γ (Δ ▹ A)) → Tm Γ (A [ π₁ σ ]T)

postulate
  [id]T : {Γ : Con} {A : Ty Γ} → A [ id ]T ≡ A
  [∘]T : {Γ Δ Θ : Con} {σ : Tms Δ Θ} {δ : Tms Γ Δ} {A : Ty Θ} → A [ σ ∘ δ ]T ≡ A [ σ ]T [ δ ]T  
  ass  : {Γ Δ Θ Ξ : Con} {σ : Tms Θ Ξ} {δ : Tms Δ Θ} {ν : Tms Γ Δ} → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
  idl  : {Γ Δ : Con} {σ : Tms Γ Δ} → id ∘ σ ≡ σ
  idr  : {Γ Δ : Con} {σ : Tms Γ Δ} → σ ∘ id ≡ σ
  ∙-η  : {Γ : Con} {σ : Tms Γ ∙} → σ ≡ ε
  ▹-β₁ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {t : Tm Γ (A [ σ ]T)}
       → π₁ (σ , t) ≡ σ
  ▹-β₂ : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ Δ} {t : Tm Γ (A [ σ ]T)}
       → (λ σ′ → Tm Γ (A [ σ′ ]T)) ⊢ π₂ (σ , t) ≡[ ▹-β₁ ]≡ t
  ▹-η  : {Γ Δ : Con} {A : Ty Δ} {σ : Tms Γ (Δ ▹ A)}
       → π₁ σ , π₂ σ ≡ σ
  π₁∘ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ ▹ A)} {δ : Tms Γ Δ}
       → π₁ (σ ∘ δ) ≡ π₁ σ ∘ δ

π₁[∘]T : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ ▹ A)} {δ : Tms Γ Δ}
  → A [ π₁ (σ ∘ δ) ]T ≡ A [ π₁ σ ]T [ δ ]T
π₁[∘]T {A = A} {σ} {δ} =
  begin
    A [ π₁ (σ ∘ δ) ]T
  ≡⟨ cong (λ π₁σ∘δ → A [ π₁σ∘δ ]T) π₁∘ ⟩
    A [ (π₁ σ) ∘ δ ]T
  ≡⟨ [∘]T ⟩
    A [ π₁ σ ]T [ δ ]T
  ∎

postulate
  π₂∘ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ ▹ A)} {δ : Tms Γ Δ}
      → Tm Γ ⊢ π₂ (σ ∘ δ) ≡[ π₁[∘]T ]≡ (π₂ σ) [ δ ]t

--  ,-∘ : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ (Θ ▹ A)} {δ : Tms Γ Δ}
--    → {!!}
-- ? ⊢ (σ ∘ δ)) ≡[ ? ]≡ (π₁ σ ∘ δ) ▹ ((π₂ σ) [ δ ]t)
    -- (σ , t) ∘ δ : Tms Γ (Θ ▹ A)
    -- (σ ∘ δ) , t [ δ ]t : Tms Γ (Θ ▹ A) ???
    

[id]t : {Γ : Con} {A : Ty Γ} {t : Tm Γ A}
  → Tm Γ ⊢ t [ id ]t ≡[ [id]T ]≡ t
[id]t {t = t} = {!!}

{-
[∘]t : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Tms Δ Θ} {δ : Tms Γ Δ} {t : Tm Θ A}
  → Tm Γ ⊢ t [ σ ∘ δ ]t ≡[ [∘]T ]≡ t [ σ ]t [ δ ]t
[∘]t {σ = σ} {δ} {t} = {!!}           
-}

{-
CON : Category
CON = Con , Tms , id , _∘_ , idl , idr , ass

1 : Terminal Category
1 = ∙ , ε , ∙-η

TY : Functor (CON op) SET
TY = Ty , _[_]T , [id]T , [∘]T

TM : Functor ((∫ TY) op) SET
TM = Tm , _[_]t , [id]t , [∘]t
-}

wk : {Γ : Con} {A : Ty Γ} → Tms (Γ ▹ A) Γ
wk = π₁ id

vz : {Γ : Con} {A : Ty Γ} → Tm (Γ ▹ A) (A [ wk ]T)
vz = π₂ id

vs : {Γ : Con} {A B : Ty Γ} → Tm Γ A → Tm (Γ ▹ B) (A [ wk ]T)
vs x = x [ wk ]t
