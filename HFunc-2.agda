{-# OPTIONS --type-in-type #-}

{- tree types, with dom and appT -}

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

{- Syntax -}

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  • : Con
  _▷_ : Con → Ty → Con

infixl 5 _▷_

dom : Ty → Con
dom set = •
dom (A ⇒ B) = dom B ▷ A

variable A B C : Ty
variable Γ Δ : Con

⟦_⟧T : Ty → Set
⟦ set ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

{-


-}
⟦_⟧m : (A : Ty) → ⟦ A ⟧T → Set
⟦_⟧h : (A : Ty) → (X : ⟦ A ⟧T) → ⟦ A ⟧m X
                → (Y : ⟦ A ⟧T) → ⟦ A ⟧m Y → Set
⟦_⟧c : (A : Ty) → (X : ⟦ A ⟧T)(XX : ⟦ A ⟧m X)
                → (Y : ⟦ A ⟧T)(YY : ⟦ A ⟧m Y)
                → (Z : ⟦ A ⟧T)(ZZ : ⟦ A ⟧m Z)
                → ⟦ A ⟧h Y YY Z ZZ
                → ⟦ A ⟧h X XX Y YY                
                → ⟦ A ⟧h X XX Z ZZ                
                

⟦ set ⟧m AA = ⊤
⟦ A ⇒ B ⟧m FF =
    Σ[ FFm ∈ ((X : ⟦ A ⟧T) → ⟦ A ⟧m X → ⟦ B ⟧m (FF X)) ]
      ((X Y : ⟦ A ⟧T)(XX : ⟦ A ⟧m X)(YY : ⟦ A ⟧m Y)
      → ⟦ A ⟧h X XX Y YY → ⟦ B ⟧h (FF X) (FFm X XX) (FF Y) (FFm Y YY))
⟦ set ⟧h X _ Y  _ = X → Y
⟦ A ⇒ B ⟧h FF (FFF , mapFF) GG (GGG , mapGG) =
  Σ[ α ∈ ((X : ⟦ A ⟧T)(XX : ⟦ A ⟧m X)
         → ⟦ B ⟧h (FF X) (FFF X XX) (GG X) (GGG X XX)) ]
    ((X Y : ⟦ A ⟧T)(XX : ⟦ A ⟧m X)(YY : ⟦ A ⟧m Y)
     → (f : ⟦ A ⟧h X XX Y YY)
     → ⟦ B ⟧c _ _ _ _ _ _ (mapGG X Y XX YY f) (α X XX) ≡
       ⟦ B ⟧c _ _ _ _ _ _ (α Y YY) (mapFF X Y XX YY f)  ) 

⟦ A ⟧c = {!!}

{-
⟦ set ⇒ set ⟧m (FF : Set → Set) =
     Σ[ FFm ∈ (X : Set) → ⊤ → ⊤ ] ,
       (X Y : Set) → ⊤ → ⊤ → (X → Y) → (FF X → FF Y)  

⟦ (set ⇒ set) ⇒ (set → set) ⟧m (FF : Set → Set)
-}


{-
α  : (X : ⟦ A ⟧T) → ⟦ B ⟧h (FF X) (GG X)
GG : ⟦ A ⟧T → ⟦ B ⟧T
FF : ⟦ A ⟧T → ⟦ B ⟧T

(f : ⟦ A ⟧h X Y) → mapGG f ∘B (α X) ≡ (α Y) ∘B mapFF f  

-}
