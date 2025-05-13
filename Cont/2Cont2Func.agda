{-# OPTIONS --type-in-type --cubical #-}

module Cont.2Cont2Func where

open import Function.Base
open import Cubical.Foundations.Prelude

open import Cont.2Cont

record 1Func (F : Set → Set) : Set₁ where
  field
    F₁ : {X Y : Set} → (X → Y) → F X → F Y
    F-id : {X : Set} → F₁ {X} id ≡ id
    F-∘ : {X Y Z : Set} (f : Y → Z) (g : X → Y)
      → F₁ (λ x → f (g x)) ≡ λ x → F₁ f (F₁ g x)

record 1Nat (F G : Set → Set) (FF : 1Func F) (GG : 1Func G) : Set₁ where
  open 1Func
  field
    η : (X : Set) → F X → G X
    nat : {X Y : Set} (f : X → Y) → η Y ∘ F₁ FF f ≡ F₁ GG f ∘ η X

idNat : {F : Set → Set} {FF : 1Func F} → 1Nat F F FF FF
idNat = record { η = λ X → id ; nat = λ f → refl }

∘Nat : {F G H : Set → Set} {FF : 1Func F} {GG : 1Func G} {HH : 1Func H}
  → 1Nat G H GG HH → 1Nat F G FF GG → 1Nat F H FF HH
∘Nat record { η = η₁ ; nat = nat₁ } record { η = η₂ ; nat = nat₂ }
  = record
  { η = λ X → η₁ X ∘ η₂ X
  ; nat = λ {X} {Y} f → cong (η₁ Y ∘_) (nat₂ f) ∙ cong (_∘ η₂ X) (nat₁ f)
  }

record 2Func : Set₁ where
  field
    H : (Set → Set) → (Set → Set)
    HH : {F : Set → Set} → 1Func F → 1Func (H F)
    H₁ : {F G : Set → Set} {FF : 1Func F} {GG : 1Func G}
      → 1Nat F G FF GG → 1Nat (H F) (H G) (HH FF) (HH GG)
    H-id : {F : Set → Set} {FF : 1Func F}
      → H₁ {F} {F} {FF} {FF} idNat ≡ idNat
    H-∘ : {F G J : Set → Set} {FF : 1Func F} {GG : 1Func G} {JJ : 1Func J}
      → (α : 1Nat G J GG JJ) (β : 1Nat F G FF GG)
      → H₁ (∘Nat α β) ≡ ∘Nat (H₁ α) (H₁ β)

