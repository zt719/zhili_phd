{-# OPTIONS --type-in-type --cubical #-}

open import Cubical.Foundations.Prelude
  hiding (J)

record Cat : Set where
  field
    Obj : Set
    Hom : Obj → Obj → Set
    id  : ∀ {X} → Hom X X 
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} {f : Hom X Y} → id ∘ f ≡ f        
    idr : ∀ {X Y} {f : Hom X Y} → f ∘ id ≡ f
    ass : ∀ {X Y Z W} {f : Hom Z W} {g : Hom Y Z} {h : Hom X Y}
        → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  _[_,_] = Hom
  _[_∘_] = _∘_
open Cat

variable C D : Cat

record Func (C D : Cat) : Set where
  field
    F₀ : Obj C → Obj D
    F₁ : ∀ {X Y} → C [ X , Y ] → D [ F₀ X , F₀ Y ]
    F-id : ∀ {X} → F₁ {X} (id C) ≡ id D
    F-∘  : ∀ {X Y Z} {f : C [ Y , Z ]} {g : C [ X , Y ]}
         → F₁ (C [ f ∘ g ]) ≡ D [ F₁ f ∘ F₁ g ]
  _₀ = F₀
  _₁ = F₁
open Func

variable F G H J : Func C D

record Nat (F G : Func C D) : Set where
  field
    ∫ : ∀ X → D [ (F ₀) X , (G ₀) X ]
    nat : ∀ {X Y} (f : C [ X , Y ])
        → D [ (G ₁) f ∘ ∫ X ] ≡ D [ ∫ Y ∘ (F ₁) f ]
  _₂ = ∫
open Nat

variable α β γ : Nat F G
  
id-Nat : Nat F F
id-Nat {C} {D} {F} = record
  { ∫ = λ X → id D
  ; nat = λ f →
      D [ (F ₁) f ∘ id D ]
    ≡⟨ idr D ⟩
      (F ₁) f
    ≡⟨ sym (idl D) ⟩
      D [ id D ∘ (F ₁) f ]
    ∎
  }

∘-Nat : {F G H : Func C D}
  → Nat G H → Nat F G → Nat F H
∘-Nat {C} {D} {F} {G} {H} α β = record
  { ∫ = λ X → D [ (α ₂) X ∘ (β ₂) X ]
  ; nat = λ {X} {Y} f →
      D [ (H ₁) f ∘ D [ (α ₂) X ∘ (β ₂) X ] ]
    ≡⟨ sym (ass D) ⟩
      D [ D [ (H ₁) f ∘ (α ₂) X ] ∘ (β ₂) X ]
    ≡⟨ cong (D [_∘ (β ₂) X ]) (nat α f) ⟩
      D [ D [ (α ₂) Y ∘ (G ₁) f ] ∘ (β ₂) X ]
    ≡⟨ ass D ⟩
      D [ (α ₂) Y ∘ D [ (G ₁) f ∘ (β ₂) X ] ]
    ≡⟨ cong (D [ (α ₂) Y ∘_]) (nat β f) ⟩
      D [ (α ₂) Y ∘ D [ (β ₂) Y ∘ (F ₁) f ] ]
    ≡⟨ sym (ass D) ⟩
      D [ D [ (α ₂) Y ∘ (β ₂) Y ] ∘ (F ₁) f ]
    ∎
  }

postulate
  Nat≡ : {C D : Cat} {F G : Func C D} {α β : Nat F G} → ∫ α ≡ ∫ β → α ≡ β

idl-Nat : ∘-Nat id-Nat α ≡ α
idl-Nat {C} {D} {F} {G} {α} = Nat≡ idl-∫
  where
  idl-∫ : (λ X → D [ id D ∘ (α ₂) X ]) ≡ α ₂
  idl-∫ i X = idl D {f = (α ₂) X} i

idr-Nat : ∘-Nat α id-Nat ≡ α
idr-Nat {C} {D} {F} {G} {α} = Nat≡ idr-∫
  where
  idr-∫ : (λ X → D [ (α ₂) X ∘ id D ]) ≡ α ₂
  idr-∫ i X = idr D {f = (α ₂) X} i

ass-Nat : {α : Nat H J} {β : Nat G H} {γ : Nat F G}
  → ∘-Nat (∘-Nat α β) γ ≡ ∘-Nat α (∘-Nat β γ)
ass-Nat {C} {D} {F} {G} {H} {J} {α} {β} {γ} = Nat≡ ass-∫
  where
  ass-∫ : (λ X → D [ D [ (α ₂) X ∘ (β ₂) X ] ∘ (γ ₂) X ]) ≡
      (λ X → D [ (α ₂) X ∘ D [ (β ₂) X ∘ (γ ₂) X ] ])
  ass-∫ i X = ass D {f = (α ₂) X} {(β ₂) X} {(γ ₂) X} i

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

[_]C : Ty → Cat
[ set ]C =
  record
  { Obj = Set
  ; Hom = λ X Y → X → Y
  ; id = λ X → X
  ; _∘_ = λ f g X → f (g X)
  ; idl = refl
  ; idr = refl
  ; ass = refl
  }
[ A ⇒ B ]C = record
  { Obj = Func [ A ]C [ B ]C
  ; Hom = Nat
  ; id = id-Nat
  ; _∘_ = ∘-Nat
  ; idl = idl-Nat
  ; idr = idr-Nat
  ; ass = λ {_} {_} {_} {_} {α} {β} {γ} → ass-Nat {α = α} {β} {γ}
  }
