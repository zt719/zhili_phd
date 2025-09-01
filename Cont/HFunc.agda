{-# OPTIONS --cubical --guardedness #-}

module Cont.HFunc where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)

record Cat (Obj : Type₁) : Type₂ where
  infixr 9 _∘_
  field
    Hom : Obj → Obj → Type₁
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    ass : ∀ {W X Y Z} (f : Hom X W) (g : Hom Y X) (h : Hom Z Y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

record Func {A B : Type₁} (ℂ : Cat A) (𝔻 : Cat B) (F : A → B) : Type₁ where
  open Cat
  field
    F₁ : ∀ {X Y} → Hom ℂ X Y → Hom 𝔻 (F X) (F Y)
    F-id : ∀ {X} → F₁ {X} (ℂ .id) ≡ 𝔻 .id
    F-∘ : ∀ {X Y Z} (f : Hom ℂ Y Z) (g : Hom ℂ X Y)
          → F₁ (ℂ ._∘_ f g ) ≡ 𝔻 ._∘_ (F₁ f) (F₁ g)

record Nat {A B : Type₁} (ℂ : Cat A) (𝔻 : Cat B)
  (F G : A → B) (FF : Func ℂ 𝔻 F) (GG : Func ℂ 𝔻 G) : Type₁ where
  open Cat
  open Func
  field
    η : ∀ X → Hom 𝔻 (F X) (G X)
    nat : ∀ {X Y} (f : Hom ℂ X Y)
      → 𝔻 ._∘_ (GG .F₁ f) (η X) ≡ 𝔻 ._∘_ (η Y) (FF .F₁ f)

postulate
  Nat≡ : {A B : Type₁} {ℂ : Cat A} {𝔻 : Cat B} {F G : A → B}
    → {FF : Func ℂ 𝔻 F} {GG : Func ℂ 𝔻 G}
    → {α β : Nat ℂ 𝔻 F G FF GG}
    → α .Nat.η ≡ β .Nat.η → α ≡ β

infixr 20 _⇒_
data Ty : Type where
  * : Ty
  _⇒_ : Ty → Ty → Ty

⟦_⟧ : Ty → Type₁
⟦ * ⟧ = Type
⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

isHFunc : {A : Ty} → ⟦ A ⟧ → Type₁

⟦_⟧HCat : (A : Ty) → Cat (Σ ⟦ A ⟧ isHFunc)

isHFunc {*} X = Lift ⊤
isHFunc {A ⇒ B} H =
  Σ[ HH ∈ ((F : ⟦ A ⟧) → isHFunc F → isHFunc (H F)) ]
  Func ⟦ A ⟧HCat ⟦ B ⟧HCat (λ (F , FF) → H F , HH F FF)

⟦ * ⟧HCat = record
  { Hom = λ (X , lift tt) (Y , lift tt) → Lift (X → Y)
  ; id = lift (λ x → x)
  ; _∘_ = λ{ (lift f) (lift g) → lift (λ x → f (g x)) }
  ; idl = λ f → refl
  ; idr = λ f → refl
  ; ass = λ f g h → refl
  }
⟦ A ⇒ B ⟧HCat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧HCat ⟦ B ⟧HCat (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG
  ; id = record
    { η = λ X → id
    ; nat = λ f → idr _ ∙ sym (idl _)
    }
  ; _∘_ = λ α β → record
    { η = λ X → α .η X ∘ β .η X
    ; nat = λ f → sym (ass _ _ _) ∙ cong (_∘ _) (α .nat f)
      ∙ (ass _ _ _) ∙ cong (_ ∘_) (β .nat f) ∙ sym (ass _ _ _)
    }
  ; idl = λ α → Nat≡ (λ i X → idl (α .η X) i)
  ; idr = λ α → Nat≡ (λ i X → idr (α .η X) i)
  ; ass = λ α β γ → Nat≡ (λ i X → ass (α .η X) (β .η X) (γ .η X) i)
  }
  where
    open Cat ⟦ B ⟧HCat
    open Nat

HFunc : Ty →  Type₁
HFunc A = Σ ⟦ A ⟧ isHFunc
