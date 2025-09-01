{-# OPTIONS --cubical --guardedness #-}

module 2Cat where

open import Level
open import Cubical.Foundations.Prelude
open import Relation.Binary.PropositionalEquality
  renaming (_≡_ to Id)

record 2Cat (ℓ₀ ℓ₁ ℓ₂ : Level) : Type (suc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
  
    -- 0-Cell
    Obj : Type ℓ₀

    -- 1-Cell
    Hom : Obj → Obj → Type ℓ₁
    isSetHom : {A B : Obj} → isSet (Hom A B)

    id₁  : {A : Obj} → Hom A A
    _∘₁_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    idl₁ : {A B : Obj} (f : Hom A B) → Id (id₁ ∘₁ f) f
    idr₁ : {A B : Obj} (f : Hom A B) → Id (f ∘₁ id₁) f
    ass₁ : {A B C D : Obj} (h : Hom C D) (g : Hom B C) (f : Hom A B) →
           Id ((h ∘₁ g) ∘₁ f) (h ∘₁ (g ∘₁ f))

    -- 2-Cell
    Two : {A B : Obj} → Hom A B → Hom A B → Type ℓ₂
    isSetTwo : {A B : Obj} {f g : Hom A B} → isSet (Two f g)
    
    id₂  : {A B : Obj} {f : Hom A B} → Two f f
    _∘₂_ : {A B : Obj} {f g h : Hom A B} → Two g h → Two f g → Two f h
    idl₂ : {A B : Obj} {f g : Hom A B} (α : Two f g) → Id (id₂ ∘₂ α) α
    idr₂ : {A B : Obj} {f g : Hom A B} (α : Two f g) → Id (α ∘₂ id₂) α
    ass₂ : {A B : Obj} {f g h k : Hom A B}
           (α : Two h k) (β : Two g h) (γ : Two f g) →
           Id ((α ∘₂ β) ∘₂ γ) (α ∘₂ (β ∘₂ γ))

    -- Horizontal Composition
    _⊗_   : {A B C : Obj} {f f' : Hom A B} {g g' : Hom B C} →
            Two f f' → Two g g' →
            Two (g ∘₁ f) (g' ∘₁ f')
    ⊗-id₂ : {A B C : Obj} {f : Hom A B} {g : Hom B C} →
            Id (id₂ {f = f} ⊗ id₂ {f = g}) id₂
    ⊗-∘₂  : {A B C : Obj} {f f' f'' : Hom A B} {g g' g'' : Hom B C}
            (α : Two f f') (α' : Two f' f'')
            (β : Two g g') (β' : Two g' g'') →
            Id ((α' ∘₂ α) ⊗ (β' ∘₂ β)) ((α' ⊗ β') ∘₂ (α ⊗ β))
