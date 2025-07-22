{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

open import Relation.Binary.PropositionalEquality

record Bush (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Bush (Bush A)
open Bush

{-# TERMINATING #-}
Bush₁ : {X Y : Set} → (X → Y)
  → Bush X → Bush Y
head (Bush₁ f bx) = f (head bx)
tail (Bush₁ f bx) = Bush₁ (Bush₁ f) (tail bx)

variable
  X Y : Set
  F G : Set → Set

_⇒_ : (Set → Set) → (Set → Set) → Set₁
F ⇒ G = {X : Set} → F X → G X

H : (Set → Set) → Set → Set
H F X = X × F (F X)

H₁ : {F₁ : {X Y : Set} → (X → Y) → F X → F Y}
  → F ⇒ G → H F ⇒ H G
H₁ {F₁ = F₁} α (x , ffx) = x , α (F₁ α ffx)

{-# TERMINATING #-}
unfold : {F : Set → Set} {F₁ : {X Y : Set} → (X → Y) → F X → F Y}
  → F ⇒ H F → F ⇒ Bush
head (unfold f a) = proj₁ (f a)
tail (unfold {F} {F₁} f a) = unfold {F} {F₁} f (F₁ (unfold {F} {F₁} f) (proj₂ (f a)))

commute : {F : Set → Set} {F₁ : {X Y : Set} → (X → Y) → F X → F Y}
  → (f : F X)
  → (α : F ⇒ H F)
  → H₁ {F} {Bush} {F₁} (unfold {F} {F₁} α) (α f)
  ≡ < head , tail > (unfold {F} {F₁} α f)
commute {X} {F} {F₁} f α = refl
