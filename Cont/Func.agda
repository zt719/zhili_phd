module Cont.Func where

open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality

private variable
  X Y Z : Set
  F G H : Set → Set

record Func (F₀ : Set → Set) : Set₁ where
  field
    F₁ : (X → Y) → F₀ X → F₀ Y
    F₁id : F₁ (id {A = X}) ≡ id
    F₁∘ : (f : Y → Z) (g : X → Y) → F₁ (f ∘ g) ≡ F₁ f ∘ F₁ g

private variable
  FF : Func F
  GG : Func G
  HH : Func H

record Nat (F G : Set → Set) (FF : Func F) (GG : Func G) : Set₁ where
  open Func FF
  open Func GG renaming (F₁ to G₁)
  field
    η : (X : Set) → F X → G X
    nat : (f : X → Y) → η Y ∘ F₁ f ≡ G₁ f ∘ η X

idNat : Nat F F FF FF
idNat = record { η = λ X → id ; nat = λ f → refl }

_∙_ : {x y z : X}
  → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

_∘Nat_ : Nat G H GG HH → Nat F G FF GG → Nat F H FF HH
record { η = η₁ ; nat = nat₁} ∘Nat record { η = η₂ ; nat = nat₂ }
  = record
  { η = λ X → η₁ X ∘ η₂ X
  ; nat = λ {X} {Y} f → cong (η₁ Y ∘_) (nat₂ f) ∙ cong (_∘ η₂ X) (nat₁ f)
  }
