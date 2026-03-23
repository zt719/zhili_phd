module Cont.HFunc where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Level

postulate
  funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
    → {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

record Cat (Obj : Set₁) : Set₂ where
  infixr 9 _∘_
  field
    Hom : Obj → Obj → Set₁
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    ass : ∀ {W X Y Z} (f : Hom X W) (g : Hom Y X) (h : Hom Z Y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

record Func {A B : Set₁} (ℂ : Cat A) (𝔻 : Cat B) (F : A → B) : Set₁ where
  open Cat
  field
    F₁ : ∀ {X Y} → Hom ℂ X Y → Hom 𝔻 (F X) (F Y)
    F-id : ∀ {X} → F₁ {X} (ℂ .id) ≡ 𝔻 .id
    F-∘ : ∀ {X Y Z} (f : Hom ℂ Y Z) (g : Hom ℂ X Y)
          → F₁ (ℂ ._∘_ f g ) ≡ 𝔻 ._∘_ (F₁ f) (F₁ g)

record Nat {A B : Set₁} (ℂ : Cat A) (𝔻 : Cat B)
  (F G : A → B) (FF : Func ℂ 𝔻 F) (GG : Func ℂ 𝔻 G) : Set₁ where
  open Cat
  open Func
  field
    η : ∀ X → Hom 𝔻 (F X) (G X)
    nat : ∀ {X Y} (f : Hom ℂ X Y)
      → 𝔻 ._∘_ (GG .F₁ f) (η X) ≡ 𝔻 ._∘_ (η Y) (FF .F₁ f)

postulate
  Nat≡ : {A B : Set₁} {ℂ : Cat A} {𝔻 : Cat B} {F G : A → B}
    → {FF : Func ℂ 𝔻 F} {GG : Func ℂ 𝔻 G}
    → {α β : Nat ℂ 𝔻 F G FF GG}
    → α .Nat.η ≡ β .Nat.η → α ≡ β

{- Syntax -}

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty
  
{- Semantics -}

⟦_⟧T : Ty → Set₁
⟦ * ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧Func : (A : Ty) → ⟦ A ⟧T → Set₁

⟦_⟧Cat : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧Func)

⟦ * ⟧Func X = Lift (suc zero) ⊤
⟦ A ⇒ B ⟧Func H =
  Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧Func F → ⟦ B ⟧Func (H F)) ]
  Func ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (F , FF) → H F , HH F FF)

⟦ * ⟧Cat = record
  { Hom = λ (X , lift tt) (Y , lift tt) → Lift (suc zero) (X → Y)
  ; id = lift (λ x → x)
  ; _∘_ = λ{ (lift f) (lift g) → lift (λ x → f (g x)) }
  ; idl = λ f → refl
  ; idr = λ f → refl
  ; ass = λ f g h → refl
  }
⟦ A ⇒ B ⟧Cat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG
  ; id = record
    { η = λ X → id
    ; nat = λ f → trans (idr _) (sym (idl _))
    }
  ; _∘_ = λ α β → record
    { η = λ X → α .η X ∘ β .η X
    ; nat = λ f → trans (sym (ass _ _ _)) (trans (cong (_∘ _) (α .nat f))
      (trans (ass _ _ _) (trans (cong (_ ∘_) (β .nat f)) (sym (ass _ _ _)))))
    }
  ; idl = λ α → Nat≡ (funExt λ X → idl (α .η X))
  ; idr = λ α → Nat≡ (funExt λ X → idr (α .η X))
  ; ass = λ α β γ → Nat≡ (funExt λ X → ass (α .η X) (β .η X) (γ .η X))
  }
  where
    open Cat ⟦ B ⟧Cat
    open Nat
