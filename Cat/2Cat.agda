{-# OPTIONS --cubical --guardedness --type-in-type #-}

module 2Cat where

open import Cubical.Foundations.Prelude

{- Strict 2-Categories -}
record 2Cat : Type where
  field
  
    -- 0-Cell
    Zero : Type

    -- 1-Cell
    One : Zero → Zero → Type
    
    id₁  : {A : Zero} → One A A
    _∘₁_ : {A B C : Zero} → One B C → One A B → One A C
    idl₁ : {A B : Zero} (f : One A B) → id₁ ∘₁ f ≡ f
    idr₁ : {A B : Zero} (f : One A B) → f ∘₁ id₁ ≡ f
    ass₁ : {A B C D : Zero} (h : One C D) (g : One B C) (f : One A B) →
           (h ∘₁ g) ∘₁ f ≡ h ∘₁ (g ∘₁ f)

    -- 2-Cell
    Two : {A B : Zero} → One A B → One A B → Type
    
    id₂  : {A B : Zero} {f : One A B} → Two f f
    _∘₂_ : {A B : Zero} {f g h : One A B} → Two g h → Two f g → Two f h
    idl₂ : {A B : Zero} {f g : One A B} (α : Two f g) → id₂ ∘₂ α ≡ α
    idr₂ : {A B : Zero} {f g : One A B} (α : Two f g) → α ∘₂ id₂ ≡ α
    ass₂ : {A B : Zero} {f g h k : One A B}
           (α : Two h k) (β : Two g h) (γ : Two f g) →
           (α ∘₂ β) ∘₂ γ ≡ α ∘₂ (β ∘₂ γ)

    isSetTwo : {A B : Zero} {f g : One A B} → isSet (Two f g)

    -- Horizontal Composition
    _⊗_   : {A B C : Zero} {f f′ : One B C} {g g′ : One A B}
          → Two g g′ → Two f f′
          → Two (f ∘₁ g) (f′ ∘₁ g′)
    ⊗-id₂ : {A B C : Zero} {f : One A B} {g : One B C}
          → (id₂ {f = f} ⊗ id₂ {f = g}) ≡ id₂
    ⊗-∘₂  : {A B C : Zero} {f f′ f′′ : One B C} {g g′ g′′ : One A B}
            (α : Two g′ g′′) (β : Two g g′)    
            (α′ : Two f′ f′′) (β′ : Two f f′)
          → (α ∘₂ β) ⊗ (α′ ∘₂ β′) ≡ (α ⊗ α′) ∘₂ (β ⊗ β′)

  Ob = Zero
  _[_,_]₁ = One
  _[_∘_]₁ = _∘₁_
  _[_,_]₂ = Two
  _[_∘_]₂ = _∘₂_
  _[_⊗_] = _⊗_
