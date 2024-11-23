open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
  hiding ([_])

record Lift {a ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field
    lower : A
open Lift

record Cat o ℓ : Set (lsuc (o ⊔ ℓ)) where
  field
    Obj : Set o
    Hom : Obj → Obj → Set ℓ
    id  : ∀ {X} → Hom X X 
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
  _[_,_] = Hom
  _[_∘_] = _∘_
open Cat

record Func {o₁ ℓ₁ o₂ ℓ₂} (C : Cat o₁ ℓ₁) (D : Cat o₂ ℓ₂) : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  field
    F₀ : Obj C → Obj D
    F₁ : ∀ {X Y} → C [ X , Y ] → D [ F₀ X , F₀ Y ]
  _₀ = F₀
  _₁ = F₁
open Func

record Nat {o₁ ℓ₁ o₂ ℓ₂} {C : Cat o₁ ℓ₁} {D : Cat o₂ ℓ₂} (F G : Func C D) : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  field
    ∫ : ∀ X → D [ (F ₀) X , (G ₀) X ]
  _₂ = ∫
open Nat

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

lone : Level
lone = lsuc lzero

-- SET is the only case of 'Cat lone lzero'
-- Naively lift it to SET′
SET : Cat lone lzero
SET =
  record
  { Obj = Set
  ; Hom = λ X Y → X → Y
  ; id = λ X → X
  ; _∘_ = λ f g X → f (g X)
  }

SET′ : Cat lone lone
SET′ =
  record
  { Obj = Set
  ; Hom = λ X Y → Lift (X → Y)
  ; id = lift (λ X → X)
  ; _∘_ = λ f g → lift (λ X → (lower f) (lower g X))
  }


[_]C : Ty → Cat lone lone
[ set ]C = SET′
[ A ⇒ B ]C = 
  record
  { Obj = Func [ A ]C [ B ]C
  ; Hom = λ F G → Nat F G
  ; id = record { ∫ = λ X → id [ B ]C }
  ; _∘_ = λ α β → record
    { ∫ = λ X → [ B ]C [ (α ₂) X ∘ (β ₂) X  ]
    }
  }

⇒/→ : Func [ set ]C [ set ]C → Set → Set
⇒/→ F X = (F ₀) X

⇒²/⇒/→ : Func [ set ⇒ set ]C [ set ⇒ set ]C → Func [ set ]C [ set ]C → Set → Set
⇒²/⇒/→ H F X = ⇒/→ ((H ₀) F) X
