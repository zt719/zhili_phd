{-# OPTIONS --cubical --guardedness #-}

module BiCat where

open import Level
open import Cubical.Foundations.Prelude

record BiCat (ℓ₀ ℓ₁ ℓ₂ : Level) : Type (suc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
  
    -- 0-Cell
    Obj : Type ℓ₀

    -- 1-Cell
    Hom : Obj → Obj → Type ℓ₁

    id₁  : {A : Obj} → Hom A A
    _∘₁_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    idl₁ : {A B : Obj} (f : Hom A B) → id₁ ∘₁ f ≡ f
    idr₁ : {A B : Obj} (f : Hom A B) → f ∘₁ id₁ ≡ f
    ass₁ : {A B C D : Obj} (h : Hom C D) (g : Hom B C) (f : Hom A B) →
           (h ∘₁ g) ∘₁ f ≡ h ∘₁ (g ∘₁ f)

    -- 2-Cell
    Two : {A B : Obj} → Hom A B → Hom A B → Type ℓ₂
    isSetTwo : {A B : Obj} {f g : Hom A B} → isSet (Two f g)
    
    id₂  : {A B : Obj} {f : Hom A B} → Two f f
    _∘₂_ : {A B : Obj} {f g h : Hom A B} → Two g h → Two f g → Two f h
    idl₂ : {A B : Obj} {f g : Hom A B} (α : Two f g) → id₂ ∘₂ α ≡ α
    idr₂ : {A B : Obj} {f g : Hom A B} (α : Two f g) → α ∘₂ id₂ ≡ α
    ass₂ : {A B : Obj} {f g h k : Hom A B}
           (α : Two h k) (β : Two g h) (γ : Two f g) →
           (α ∘₂ β) ∘₂ γ ≡ α ∘₂ (β ∘₂ γ)

    -- Horizontal Composition
    _⊗_   : {A B C : Obj} {f f' : Hom B C} {g g' : Hom A B} →
            Two f f' → Two g g' →
            Two (f ∘₁ g) (f' ∘₁ g')
    ⊗-id₂ : {A B C : Obj} {f : Hom B C} {g : Hom A B} →
            id₂ {f = f} ⊗ id₂ {f = g} ≡ id₂
    ⊗-∘₂  : {A B C : Obj} {f f' f'' : Hom B C} {g g' g'' : Hom A B}
            (α : Two f f') (α' : Two f' f'')
            (β : Two g g') (β' : Two g' g'') →
            (α' ∘₂ α) ⊗ (β' ∘₂ β) ≡ (α' ⊗ β') ∘₂ (α ⊗ β)

    -- Coherence
    α : {A B C D : Obj}
        {f : Hom C D} {g : Hom B C} {h : Hom A B} →
        Two (f ∘₁ (g ∘₁ h)) ((f ∘₁ g) ∘₁ h)
    ƛ : {A B : Obj} {f : Hom A B} → Two (id₁ ∘₁ f) f
    ρ : {A B : Obj} {f : Hom A B} → Two (f ∘₁ id₁) f
    tri : {A B C : Obj} {f : Hom B C} {g : Hom A B} →
          id₂ {f = f} ⊗ ƛ ≡ (ρ ⊗ id₂ {f = g}) ∘₂ α
    penta : {A B C D E : Obj}
            {f : Hom D E} {g : Hom C D}
            {h : Hom B C} {k : Hom A B} →
            ((α {f = f} {g = g} {h = h} ⊗ id₂ {f = k}) ∘₂ α) ∘₂ (id₂ ⊗ α)
            ≡ α ∘₂ α

