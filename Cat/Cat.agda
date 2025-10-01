{-# OPTIONS --cubical --guardedness --type-in-type #-}

module Cat where

open import Cubical.Foundations.Prelude

record Cat : Type where
  field
    Obj : Type
    Hom : Obj → Obj → Type
    isSetHom : {A B : Obj} → isSet (Hom A B)
    id  : {A : Obj} → Hom A A
    _∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    idl : {A B : Obj} (f : Hom A B) → id ∘ f ≡ f
    idr : {A B : Obj} (f : Hom A B) → f ∘ id ≡ f
    ass : {A B C D : Obj} (h : Hom C D) (g : Hom B C) (f : Hom A B) →
           (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
