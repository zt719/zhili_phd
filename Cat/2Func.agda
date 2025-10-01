{-# OPTIONS --cubical --guardedness --type-in-type #-}

module 2Func where

open import Cubical.Foundations.Prelude
open import 2Cat

record 2Func (ℂ : 2Cat) (𝔻 : 2Cat) : Type where
  open 2Cat.2Cat
  field
    F₀    : Ob ℂ → Ob 𝔻
    
    F₁    : {A B : Ob ℂ} → ℂ [ A , B ]₁ → 𝔻 [ F₀ A , F₀ B ]₁
    F-id₁ : {A : Ob ℂ} → F₁ (ℂ .id₁ {A = A}) ≡ 𝔻 .id₁
    F-∘₁  : {A B C : Ob ℂ} (f : ℂ [ B , C ]₁) (g : ℂ [ A , B ]₁)
      → F₁ (ℂ [ f ∘ g ]₁) ≡ 𝔻 [ F₁ f ∘ F₁ g ]₁
    
    F₂    : {A B : Ob ℂ} {f g : ℂ [ A , B ]₁}
      → ℂ [ f , g ]₂ → 𝔻 [ F₁ f , F₁ g ]₂
    F-id₂ : {A B : Ob ℂ} {f : ℂ [ A , B ]₁}
      → F₂ (ℂ .id₂ {f = f}) ≡ 𝔻 .id₂
    F-∘₂  : {A B : Ob ℂ} {f g h : ℂ [ A , B ]₁}
      → (α : ℂ [ g , h ]₂) (β : ℂ [ f , g ]₂)
      → F₂ (ℂ [ α ∘ β ]₂) ≡ 𝔻 [ F₂ α ∘ F₂ β ]₂

    F-⊗   : {A B C : Ob ℂ} {f f′ : ℂ [ B , C ]₁} {g g′ : ℂ [ A , B ]₁}
      → (α : ℂ [ g , g′ ]₂) (β : ℂ [ f , f′ ]₂)
      → subst2 (𝔻 .Two) (F-∘₁ f g) (F-∘₁ f′ g′) (F₂ (ℂ [ α ⊗ β ])) ≡ 𝔻 [ F₂ α ⊗ F₂ β ]
