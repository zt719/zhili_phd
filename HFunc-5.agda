{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
  hiding (J)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

variable o o₁ o₂ h h₁ h₂ : Level

record Cat (o h : Level) : Type (lsuc (o ⊔ h)) where
  field
    Obj : Type o
    Hom : Obj → Obj → Type h
    Hom-set : ∀ {X Y} → isSet (Hom X Y)
    id  : ∀ {X} → Hom X X 
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} {f : Hom X Y} → id ∘ f ≡ f        
    idr : ∀ {X Y} {f : Hom X Y} → f ∘ id ≡ f
    ass : ∀ {X Y Z W} {f : Hom Z W} {g : Hom Y Z} {h : Hom X Y}
        → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  _[_,_] = Hom
  _[_∘_] = _∘_
open Cat

record Func (C : Cat o₁ h₁) (D : Cat o₂ h₂): Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂) where
  field
    F₀ : Obj C → Obj D
    F₁ : ∀ {X Y} → C [ X , Y ] → D [ F₀ X , F₀ Y ]
    F-id : ∀ {X} → F₁ {X} (id C) ≡ id D
    F-∘  : ∀ {X Y Z} {f : C [ Y , Z ]} {g : C [ X , Y ]}
         → F₁ (C [ f ∘ g ]) ≡ D [ F₁ f ∘ F₁ g ]
  _₀ = F₀
  _₁ = F₁
open Func

record Nat {C : Cat o₁ h₁} {D : Cat o₂ h₂}
  (F G : Func C D) : Type (o₁ ⊔ h₁ ⊔ h₂) where
  field
    ∫ : ∀ X → D [ (F ₀) X , (G ₀) X ]
    nat : ∀ {X Y} (f : C [ X , Y ])
        → D [ (G ₁) f ∘ ∫ X ] ≡ D [ ∫ Y ∘ (F ₁) f ]
  _₂ = ∫
  
open Nat

id-Nat : {C : Cat o₁ h₁} {D : Cat o₂ h₂} {F : Func C D}
  → Nat F F
id-Nat {C = C} {D} {F} = record
  { ∫ = λ X → id D
  ; nat = λ f →
      D [ (F ₁) f ∘ id D ]
    ≡⟨ idr D ⟩
      (F ₁) f
    ≡⟨ sym (idl D) ⟩
      D [ id D ∘ (F ₁) f ]
    ∎
  }

∘-Nat : {C : Cat o₁ h₁} {D : Cat o₂ h₂} {F G H : Func C D}
  → Nat G H → Nat F G → Nat F H
∘-Nat {C = C} {D} {F} {G} {H} α β = record
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

Nat≡ : {C : Cat o₁ h₁} {D : Cat o₂ h₂}
     → {F G : Func C D} {α β : Nat F G}
     → (∀ X → (α ₂) X ≡ (β ₂) X)
     → α ≡ β
∫ (Nat≡ path i) X = path X i
nat (Nat≡ {D = D} {F} {G} {α} {β} path i) {X} {Y} f = 
  isProp→PathP
    (λ i → Hom-set D (D [ (G ₁) f ∘ path X i ]) (D [ path Y i ∘ (F ₁) f ]))
    (nat α f) (nat β f) i

postulate
  Nat-isSet : {C : Cat o₁ h₁} {D : Cat o₂ h₂} {F G : Func C D}
            → isSet (Nat F G)

idl-Nat : {C : Cat o₁ h₁} {D : Cat o₂ h₂} {F G : Func C D}
        → {α : Nat F G} → ∘-Nat id-Nat α ≡ α
idl-Nat {D = D} = Nat≡ (λ X → idl D)

idr-Nat : {C : Cat o₁ h₁} {D : Cat o₂ h₂} {F G : Func C D}
        → {α : Nat F G} → ∘-Nat α id-Nat ≡ α
idr-Nat {D = D} = Nat≡ (λ X → idr D)

ass-Nat : {C : Cat o₁ h₁} {D : Cat o₂ h₂} {F G H J : Func C D}
        → {α : Nat H J} {β : Nat G H} {γ : Nat F G}
  → ∘-Nat (∘-Nat α β) γ ≡ ∘-Nat α (∘-Nat β γ)
ass-Nat {D = D} = Nat≡ (λ X → ass D)

data Ty : Type where
  set : Ty
  _⇒_ : Ty → Ty → Ty

record n-Type n : Type₁ where
  field
    ∣_∣   : Type
    is-tr : isOfHLevel n ∣_∣
open n-Type

Set′ : Type₁
Set′ = n-Type 2

[_]o : Ty → Level
[_]h : Ty → Level
[_]C : (A : Ty) → Cat [ A ]o [ A ]h

[ set ]o = ℓ-suc ℓ-zero
[ A ⇒ B ]o = [ A ]o ⊔ [ A ]h ⊔ [ B ]o ⊔ [ B ]h

[ set ]h = ℓ-zero
[ A ⇒ B ]h = [ A ]o ⊔ [ A ]h ⊔ [ B ]h

[ set ]C .Obj = Set′
[ set ]C .Hom X Y = ∣ X ∣ → ∣ Y ∣
[ set ]C .Hom-set {X} {Y} f g p q i j x =
  is-tr Y (f x) (g x) (funExt⁻ p x) (funExt⁻ q x) i j
[ set ]C .id X = X
[ set ]C ._∘_ f g X = f (g X)
[ set ]C .idl = refl
[ set ]C .idr = refl
[ set ]C .ass = refl
[ A ⇒ B ]C .Obj = Func [ A ]C [ B ]C
[ A ⇒ B ]C .Hom = Nat
[ A ⇒ B ]C .Hom-set = Nat-isSet
[ A ⇒ B ]C .id = id-Nat
[ A ⇒ B ]C ._∘_ = ∘-Nat
[ A ⇒ B ]C .idl = idl-Nat
[ A ⇒ B ]C .idr = idr-Nat
[ A ⇒ B ]C .ass {_} {_} {_} {_} {α} {β} {γ}
  = ass-Nat {α = α} {β} {γ}
