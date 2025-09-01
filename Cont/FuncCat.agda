open import Level
-- open import Relation.Binary.PropositionalEquality hiding ([_])

record Cat o ℓ : Set (suc (o ⊔ ℓ)) where
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
  * : Ty
  _⇒_ : Ty → Ty → Ty

SET : Cat (suc zero) (suc zero)
SET = 
  record
  { Obj = Set
  ; Hom = λ X Y → Lift (suc zero) (X → Y)
  ; id = lift (λ X → X)
  ; _∘_ = λ f g → lift (λ X → (lower f) (lower g X))
  }

⟦_⟧Cat : Ty → Cat (suc zero) (suc zero)
⟦ * ⟧Cat = SET
⟦ A ⇒ B ⟧Cat = 
  record
  { Obj = Func ⟦ A ⟧Cat ⟦ B ⟧Cat
  ; Hom = λ F G → Nat F G
  ; id = record { ∫ = λ X → id ⟦ B ⟧Cat }
  ; _∘_ = λ α β → record
    { ∫ = λ X → ⟦ B ⟧Cat [ (α ₂) X ∘ (β ₂) X  ]
    }
  }

example : Func ⟦ * ⇒ * ⟧Cat ⟦ * ⇒ * ⟧Cat → Func ⟦ * ⟧Cat ⟦ * ⟧Cat → Set → Set
example FuncH FuncF X = (((FuncH ₀) FuncF) ₀) X

cannot : Func ⟦ * ⇒ * ⟧Cat ⟦ * ⇒ * ⟧Cat → (Set → Set) → Set → Set
cannot FuncH F X = {!!}
