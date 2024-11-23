{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
  hiding ([_])
open ≡-Reasoning

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

record Func (C D : Cat) : Set where
  open Cat
  field
    F₀ : Obj C → Obj D
    F₁ : ∀ {X Y} → C [ X , Y ] → D [ F₀ X , F₀ Y ]
    F-id : ∀ {X} → F₁ {X} (id C) ≡ id D
    F-∘  : ∀ {X Y Z} {f : C [ Y , Z ]} {g : C [ X , Y ]}
         → F₁ (C [ f ∘ g ]) ≡ D [ F₁ f ∘ F₁ g ]

  _₀ = F₀
  _₁ = F₁
  
record Nat {C D} (F G : Func C D) : Set where
  open Cat
  open Func
  field
    ∫ : ∀ X → D [ (F ₀) X , (G ₀) X ]
    nat : ∀ {X Y} (f : C [ X , Y ])
        → D [ (G ₁) f ∘ ∫ X ] ≡ D [ ∫ Y ∘ (F ₁) f ]
  _₂ = ∫

postulate
  nat≡ : ∀ {C D} {F G : Func C D} (α β : Nat F G) → Nat.∫ α ≡ Nat.∫ β → α ≡ β

idNat : ∀ {C D} {F : Func C D} → Nat F F
idNat {C} {D} {F} = record { ∫ = λ X → id ; nat = λ f → nat′ f }
  where
  open Cat using (_[_,_])
  open Cat D hiding (_[_,_])
  open Func
  nat′ : ∀ {X Y} (f : C [ X , Y ]) → (F ₁) f ∘ id ≡ id ∘ (F ₁) f
  nat′ f =
    begin
      (F ₁) f ∘ id
    ≡⟨ idr ⟩
      (F ₁) f
    ≡⟨ sym idl ⟩
      id ∘ (F ₁) f
    ∎

seC : Cat
Cat₁ =
  record
  { Obj = Set
  ; Hom = λ X Y → X → Y
  ; id = λ X → X
  ; _∘_ = λ f g X → f (g X)
  ; idl = refl
  ; idr = refl
  ; ass = refl
  }

Cat₂ : Cat
Cat₂ =
  record
  { Obj = Func Cat₁ Cat₁
  ; Hom = λ F G → Nat F G
  ; id = record
    { ∫ = λ X → id
    ; nat = λ f → refl
    }
  ; _∘_ = λ α β → record
    { ∫ = λ X → (α ₂) X ∘ (β ₂) X
    ; nat = λ f → nat′ {α = α} {β = β} f
    }
  ; idl = {!!}
  ; idr = {!!}
  ; ass = {!!}
  }
  where
  open Cat Cat₁
  open Func
  open Nat
  nat′ : {F G H : Func Cat₁ Cat₁} {α : Nat G H} {β : Nat F G}
         {X Y : Set} (f : X → Y)
       → (H ₁) f ∘ ((α ₂) X ∘ (β ₂) X)
       ≡ (((α ₂) Y) ∘ ((β ₂) Y)) ∘ (F ₁) f
  nat′ {F} {G} {H} {α} {β} {X} {Y} f =
    begin
      (H ₁) f ∘ ((α ₂) X ∘ (β ₂) X)
    ≡⟨ sym (ass {f = (H ₁) f} {g = (α ₂) X}) ⟩
      ((H ₁) f ∘ (α ₂) X) ∘ (β ₂) X
    ≡⟨ cong (_∘ (β ₂) X) (nat α f) ⟩
      ((α ₂) Y ∘ (G ₁) f) ∘ (β ₂) X
    ≡⟨ ass {f = (α ₂) Y} {g = (G ₁) f}⟩
      (α ₂) Y ∘ ((G ₁) f ∘ (β ₂) X)
    ≡⟨ cong ((α ₂) Y ∘_) (nat β f) ⟩
      (α ₂) Y ∘ ((β ₂) Y ∘ (F ₁) f)
    ≡⟨ sym (ass {f = (α ₂) Y} {g = (β ₂) Y})⟩
      ((α ₂) Y ∘ (β ₂) Y) ∘ (F ₁) f
    ∎

  idl′ : {F G : Func Cat₁ Cat₁} {α : Nat F G}
       → record { ∫ = α ₂ ; nat = nat α } ≡ α
  idl′ {F} {G} {α} = {!!}
  

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

[_]C : Ty → Cat
[ set ]C = Cat₁
[ A ⇒ B ]C =
  record
   { Obj = Func [ A ]C [ B ]C
   ; Hom = Nat
   ; id = record { ∫ = λ X → id [ B ]C ; nat = λ f → {!!}}
   ; _∘_ = λ α β → record
     { ∫ = λ X → [ B ]C [ (α ₂) X ∘ (β ₂) X  ]
     ; nat = {!!}
     }
   ; idl = {!!}
   ; idr = {!!}
   ; ass = {!!}
   }
  where
  open Cat
  open Func
  open Nat
