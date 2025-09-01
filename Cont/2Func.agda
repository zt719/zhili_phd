module Cont.2Func where

open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality

variable
  X Y Z : Set

record Func (F : Set → Set) : Set₁ where
  field
    F₁ : (X → Y) → F X → F Y
    F₁id : F₁ (id {A = X}) ≡ id
    F₁∘ : (f : Y → Z) (g : X → Y) → F₁ (f ∘ g) ≡ F₁ f ∘ F₁ g

variable
  F G : Set → Set
  FF GG : Func F

record Nat (F G : Set → Set) (FF : Func F) (GG : Func G) : Set₁ where
  open Func FF
  open Func GG renaming (F₁ to G₁)
  field
    η : (X : Set) → F X → G X
    nat : (f : X → Y) → η Y ∘ F₁ f ≡ G₁ f ∘ η X

idNat : Nat F F FF FF
idNat = record { η = λ X → id ; nat = λ f → refl }

_∙_ : {x y z : X} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

_∘Nat_ : {H : Set → Set} {HH : Func H}
  → Nat G H GG HH → Nat F G FF GG → Nat F H FF HH
record { η = η₁ ; nat = nat₁} ∘Nat record { η = η₂ ; nat = nat₂ }
  = record
  { η = λ X → η₁ X ∘ η₂ X
  ; nat = λ {X} {Y} f → cong (η₁ Y ∘_) (nat₂ f) ∙ cong (_∘ η₂ X) (nat₁ f)
  }

variable
  α β : Nat F G FF GG



{-

record 2Func (H : (Set → Set) → Set → Set) : Set₁ where
  field
    H₀ : Func F → Func (H F)
    H₁ : Nat F G FF GG → Nat (H F) (H G) (H₀ FF) (H₀ GG)
    H₁id : H₁ {F} {_} {FF} idNat ≡ idNat
    H₁∘ : H₁ (α ∘Nat β) ≡ H₁ α ∘Nat H₁ β
    
variable
  H : (Set → Set) → Set → Set
  HH : 2Func H

record 2Nat (H J : (Set → Set) → Set → Set)
  (HH : 2Func H) (JJ : 2Func J) : Set₁ where
  open 2Func HH
  open 2Func JJ renaming (H₁ to J₁)
  open Nat
  field
    2η : (F : Set → Set) (X : Set) → H F X → J F X
    nat :  (α : Nat F G FF GG) (f : X → Y)
      → 2η G X ∘ H₁ α .η X ≡ J₁ α .η X ∘ 2η F X
-}
