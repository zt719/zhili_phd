module Cont.Cat where

open import Level

variable
  o h o' h' : Level

record Category {o h} : Set (suc (o ⊔ h)) where
  field
    Obj : Set o
    Hom : Obj → Obj → Set h
    id  : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    
  ∣_∣ = Obj
  _[_,_] = Hom
  _[_∘_] = _∘_
open Category using (∣_∣; _[_,_])  

record Functor {o h o' h'} (ℂ : Category {o} {h})
  (𝔻 : Category {o'} {h'}) : Set (o ⊔ h ⊔ o' ⊔ h') where
  field
    F₀ : ∣ ℂ ∣ → ∣ 𝔻 ∣
    F₁ : ∀ {X Y} → ℂ [ X , Y ] → 𝔻 [ F₀ X , F₀ Y ]
    
  _₀ = F₀
  _₁ = F₁
open Functor using (_₀; _₁)

record NatTrans {o h o' h'} {ℂ : Category {o} {h}}
  {𝔻 : Category {o'} {h'}} (F G : Functor ℂ 𝔻)
  : Set (o ⊔ h ⊔ h') where
  field
    α : (X : ∣ ℂ ∣) → 𝔻 [ (F ₀) X , (G ₀) X ]

