open import Relation.Binary.PropositionalEquality
open import Function.Base

variable X Y A B : Set

record Func : Set₁ where
  constructor _,_
  field
    F : Set → Set
    F₁ : (X → Y) → F X → F Y

variable FF GG : Func

Alg : Func → Set → Set
Alg (F , _) A = F A → A

{-
record AlgHom (FF : Func) (A B : Set) (alg₁ : Alg FF A) (alg₂ : Alg FF B) : Set₁ where
  constructor _,_
  field
    f : A → B
--    commute : (x : F A) → f (α x) ≡ β (F₁ f x)
-}

open import Data.Sum
  renaming ([_,_] to case)

_⊎Func_ : Func → Func → Func
(F , F₁) ⊎Func (G , G₁) = F⊎G , F⊎G₁
  where
  F⊎G : Set → Set
  F⊎G X = F X ⊎ G X

  F⊎G₁ : (X → Y) → F⊎G X → F⊎G Y
  F⊎G₁ f (inj₁ a) = inj₁ (F₁ f a)
  F⊎G₁ f (inj₂ b) = inj₂ (G₁ f b)

_⊎Alg_ : Alg FF A → Alg GG A → Alg (FF ⊎Func GG) A
(α ⊎Alg β) (inj₁ x) = α x
(α ⊎Alg β) (inj₂ y) = β y

