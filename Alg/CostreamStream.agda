{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

variable
  X Y A : Set
  F G : Set → Set

data Costream (A : Set) : Set where
  _∷_ : A → Costream A → Costream A

fold : (f : A × X → X)
  → Costream A → X
fold f (a ∷ as) = f (a , fold f as)

{- Costream A ≃ ⊥ -}
open import Data.Empty

to : Costream A → ⊥
to (a ∷ as) = to as

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

unfold : (f : X → A × X)
  → X → Stream A
head (unfold f x) = proj₁ (f x)
tail (unfold f x) = unfold f (proj₂ (f x))

-- Higher --

H : (Set → Set) → Set → Set
H F X = X × F X

H₁ : (F X → G X) → H F X → H G X
H₁ α (x , fx) = x , α fx

unf : (f : F X → H F X)
  → F X → Stream X
head (unf f x) = proj₁ (f x)
tail (unf {X} {F} f x) = unf {X} {F} f (proj₂ (f x))

open import Relation.Binary.PropositionalEquality

com : (a : F X) (α : F X → H F X) 
  → H₁ {F} {X} {Stream} (unf {F} {X} α) (α a) ≡ < head , tail > (unf {F} {X} α a)
com {F} {X} a α₁ = refl
