{-# OPTIONS --type-in-type --cubical #-}

module Cont.HFunc where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

⟦_⟧T : Ty → Set
⟦ * ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

record Cat (Obj : Set) : Set where
  field
    Hom : Obj → Obj → Set
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    ass : ∀ {W X Y Z} (f : Hom X W) (g : Hom Y X) (h : Hom Z Y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  infixr 9 _∘_

record Func {X Y : Set} (C : Cat X)(D : Cat Y)(F : X → Y) : Set where
  open Cat
  open Cat C renaming (_∘_ to _∘C_)
  open Cat D renaming (_∘_ to _∘D_)  
  field
    fmap : ∀ {X Y} → Hom C X Y → Hom D (F X) (F Y)
    fmapid : ∀ {X} → fmap {X} (id C) ≡ id D
    fmap∘ : ∀ {X Y Z} (f : Hom C Y Z) (g : Hom C X Y)
          → fmap (f ∘C g) ≡ (fmap f) ∘D (fmap g)

record Nat {X Y : Set}(C : Cat X)(D : Cat Y)(F G : X → Y)
           (FF : Func C D F)(GG : Func C D G) : Set where
  open Cat
  open Cat D renaming (_∘_ to _∘D_)
  open Func
  field
    η : ∀ X → Hom D (F X) (G X)
    nat : ∀ {X Y} (f : Hom C X Y) →
          fmap GG f ∘D η X ≡ η Y ∘D fmap FF f

postulate
  Nat≡ : {X Y : Set} {C : Cat X} {D : Cat Y} {F G : X → Y}
    → {FF : Func C D F} {GG : Func C D G}
    → {α β : Nat C D F G FF GG}
    → Nat.η α ≡ Nat.η β
    → α ≡ β

⟦_⟧Func : (A : Ty) → ⟦ A ⟧T → Set
⟦_⟧Cat : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧Func)

⟦ * ⟧Func X = ⊤
⟦ A ⇒ B ⟧Func H = Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧Func F → ⟦ B ⟧Func (H F)) ]
               Func ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (F , FF) → H F , HH F FF)

⟦ * ⟧Cat = record
  { Hom = λ (X , _) (Y , _) → X → Y
  ; id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; idl = λ f → refl
  ; idr = λ f → refl
  ; ass = λ f g h → refl
  }

⟦ A ⇒ B ⟧Cat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG

  ; id = record { η = λ X → id ; nat = λ f → idr _ ∙ sym (idl _) }
  ; _∘_ = λ{ record { η = η₁ ; nat = nat₁ } record { η = η₂ ; nat = nat₂ }
    → record { η = λ X → η₁ X ∘ η₂ X ; nat = λ f → sym (ass _ _ _) ∙ cong (_∘ _) (nat₁ f)
              ∙ (ass _ _ _) ∙ cong (_ ∘_) (nat₂ f) ∙ sym (ass _ _ _) } }
  ; idl = λ α → Nat≡ (λ i X → idl (α .Nat.η X) i)
  ; idr = λ α → Nat≡ (λ i X → idr (α .Nat.η X) i)
  ; ass = λ α β γ → Nat≡ (λ i X → ass (α .Nat.η X) (β .Nat.η X) (γ .Nat.η X) i)
  }
  where
    open Cat ⟦ B ⟧Cat
