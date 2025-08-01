module Cont.2Func where

open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality

open import Cont.Func

private variable
  X Y : Set
  F₀ G₀ : Set → Set
  FF : Func F₀
  GG : Func G₀

variable
  α β : Nat F₀ G₀ FF GG

record 2Func (H₀ : (Set → Set) → Set → Set) : Set₁ where
  field
    H' : Func F₀ → Func (H₀ F₀)
    H₁ : Nat F₀ G₀ FF GG → Nat (H₀ F₀) (H₀ G₀) (H' FF) (H' GG)
    H₁id : H₁ {F₀} {_} {FF} idNat ≡ idNat
    H₁∘ : H₁ (α ∘Nat β) ≡ H₁ α ∘Nat H₁ β
    
variable
  H₀ : (Set → Set) → Set → Set
  HH : 2Func H₀

record 2Nat (H₀ J₀ : (Set → Set) → Set → Set)
  (H : 2Func H₀) (J : 2Func J₀) : Set₁ where
  open 2Func H
  open 2Func J renaming (H₁ to J₁)
  open Nat
  field
    2η : (F₀ : Set → Set) (X : Set) → H₀ F₀ X → J₀ F₀ X
    nat :  (α : Nat F₀ G₀ FF GG) (f : X → Y)
      → 2η G₀ X ∘ H₁ α .η X ≡ J₁ α .η X ∘ 2η F₀ X
