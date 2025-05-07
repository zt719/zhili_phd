{-# OPTIONS --type-in-type --cubical #-}

open import Cubical.Foundations.Prelude

record Cat : Set where
  field
    Obj : Set
    Hom : Obj → Obj → Set
    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    idl : ∀ {A B} (f : Hom A B) → id ∘ f ≡ f
    idr : ∀ {A B} (f : Hom A B) → f ∘ id ≡ f
    ass : ∀ {A B C D} (f : Hom C D) (g : Hom B C) (h : Hom A B)
      → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h

  ∣_∣ = Obj
  _[_,_] = Hom
  _[_∘_] = _∘_
  
open Cat

record Func (ℂ 𝔻 : Cat) : Set where
  constructor _,_
  field
    F₀ : ∣ ℂ ∣ → ∣ 𝔻 ∣
    F₁ : ∀ {A B} → ℂ [ A , B ] → 𝔻 [ F₀ A , F₀ B ]
    F-id : ∀ {A} → F₁ {A} (ℂ .id) ≡ 𝔻 .id
    F-∘  : ∀ {A B C} (f : ℂ [ B , C ]) (g : ℂ [ A , B ])
      → F₁ (ℂ [ f ∘ g ]) ≡ 𝔻 [ F₁ f ∘ F₁ g ]
open Func

record NatTrans {ℂ 𝔻} (F G : Func ℂ 𝔻) : Set where
  field
    η : ∀ A → 𝔻 [ F .F₀ A , G .F₀ A ]
    nat : ∀ {A B} (f : ℂ [ A , B ]) → 𝔻 [ η B ∘ F .F₁ f ] ≡ 𝔻 [ G .F₁ f ∘ η A ]
open NatTrans    

module Loc (ℂ : Cat)
  (_×_ : ∣ ℂ ∣ → ∣ ℂ ∣ → ∣ ℂ ∣)
  (π₁ : ∀ {A B} → ℂ [ A × B , A ])
  (π₂ : ∀ {A B} → ℂ [ A × B , B ])
  (<_,_> : ∀ {A B C} → ℂ [ A , B ] → ℂ [ A , C ] → ℂ [ A , B × C ])
  (π₁∘<> : ∀ {A B C} (f : ℂ [ A , B ]) (g : ℂ [ A , C ])
    → ℂ [ π₁ ∘ < f , g > ] ≡ f)
  (π₂∘<> : ∀ {A B C} (f : ℂ [ A , B ]) (g : ℂ [ A , C ])
    → ℂ [ π₂ ∘ < f , g > ] ≡ g)
  (<>∘ : ∀ {A B C D} (f : ℂ [ A , B ]) (g : ℂ [ A , C ]) (h : ℂ [ D , A ])
    → ℂ [ < f , g > ∘ h ] ≡ < ℂ [ f ∘ h ] , ℂ [ g ∘ h ] >)
  (<>-η : ∀ {A B} → < π₁ {A} {B} , π₂ > ≡ ℂ .id)
  where

  LOC : (Γ : ∣ ℂ ∣) → Cat
  LOC Γ .Obj = ∣ ℂ ∣
  LOC Γ .Hom A B = ℂ [ Γ × A , B ]
  LOC Γ .id = π₂
  LOC Γ ._∘_ f g = ℂ [ f ∘ < π₁ , g > ]
  LOC Γ .idl f = π₂∘<> π₁ f
  LOC Γ .idr f = cong (ℂ [ f ∘_]) <>-η ∙ ℂ .idr f
  LOC Γ .ass f g h = _

  {-
  record stFunc (Γ : ∣ ℂ ∣) : Set where
    field
      LF₀ : ∣ LOC Γ ∣ → ∣ LOC Γ ∣
      LF₁ : ∀ {A B} → LOC Γ [ A , B ] → LOC Γ [ LF₀ A , LF₀ B ]
      LF-id : ∀ {A} → LF₁ {A} (LOC Γ .id) ≡ LOC Γ .id
      LF-∘  : ∀ {A B C} (f : LOC Γ [ B , C ]) (g : LOC Γ [ A , B ])
        → LF₁ (LOC Γ [ f ∘ g ]) ≡ LOC Γ [ LF₁ f ∘ LF₁ g ]
  -}
  
  stFunc : (Γ : ∣ ℂ ∣) → Set
  stFunc Γ = Func (LOC Γ) (LOC Γ)

{-
  stFunc-nat : (Γ : ∣ ℂ ∣) (F G : stFunc Γ) → NatTrans F G
  stFunc-nat Γ F G .η = {!!}
  stFunc-nat Γ F G .nat = {!!}
-}
