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

record Cat (Obj : Set) : Set where
  field
    Hom : Obj → Obj → Set
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    ass : ∀ {W X Y Z}{f : Hom X W}{g : Hom Y X}{h : Hom Z Y}
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

open Cat

record Func {X Y : Set}(C : Cat X)(D : Cat Y)(F : X → Y) : Set where
  open Cat C renaming (_∘_ to _∘C_)
  open Cat D renaming (_∘_ to _∘D_)  
  field
    fmap : ∀ {X Y} → Hom C X Y → Hom D (F X) (F Y) 
    fmap∘ : ∀ {X Y Z}{f : Hom C Y Z}{g : Hom C X Y}
          → fmap (f ∘C g) ≡ (fmap f) ∘D (fmap g)

open Func

record Nat {X Y : Set}(C : Cat X)(D : Cat Y)(F G : X → Y)
           (FF : Func C D F)(GG : Func C D G) : Set where
  open Cat D renaming (_∘_ to _∘D_)  
  field
    α : (x : X) → Hom D (F x) (G x)
    nat : {x y : X}(f : Hom C x y) →
          fmap GG f ∘D α x ≡ α y ∘D fmap FF f
               
⟦_⟧F : (A : Ty) → ⟦ A ⟧T → Set
⟦_⟧C : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧F)

⟦ set ⟧F X = ⊤
⟦ A ⇒ B ⟧F F = Σ[ FF ∈ ((X : ⟦ A ⟧T) → ⟦ A ⟧F X → ⟦ B ⟧F (F X)) ]
               Func ⟦ A ⟧C ⟦ B ⟧C λ (X , XX) → (F X) , (FF X XX)

⟦ set ⟧C = record { Hom = λ (X , _) (Y , _) → X → Y
                 ; _∘_ = λ f g x → f (g x)
                 ; ass = refl }

⟦ A ⇒ B ⟧C = record { Hom = λ (F , FF , FFF) (G , GG , GGG) → {!!} ; _∘_ = {!!} ; ass = {!!} }
{-                 
⟦ A ⇒ B ⟧C = record {
        Hom = λ (F , (FF , FFF)) (G , (GG , GGG)) →
          Nat ⟦ A ⟧C ⟦ B ⟧C (λ (A , AA) → F A  , FF A AA)
                           (λ (A , AA) → G A  , GG A AA) FFF GGG
       ; _∘_ = {!!} ; ass = {!!} }
      where open Cat ⟦ A ⟧C
-}
{-
⟦ A ⇒ B ⟧C :
Cat (Σ ⟦ A ⇒ B ⟧T ⟦ A ⇒ B ⟧F)
= Cat (Σ (F ∈ ⟦ A ⟧T → ⟦ B ⟧T) (⟦ A ⇒ B ⟧F F))
= Cat (Σ (F ∈ ⟦ A ⟧T → ⟦ B ⟧T)
      (Σ FF : (X : ⟦ A ⟧T) → ⟦ A ⟧F X → ⟦ B ⟧F (F X))
         Func ⟦ A ⟧C ⟦ B ⟧C λ (X , XX) → (F X) , (FF X XX)

-}
