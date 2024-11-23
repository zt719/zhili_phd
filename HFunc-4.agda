{-# OPTIONS --type-in-type #-}

{- tree types, with dom and appT -}

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Nat

{- Syntax -}

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

⟦_⟧T : Ty → Set
⟦ set ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

-- f : ℕ → ℕ
-- mono f = m ≤ n → f m ≤ f n

-- f g : ℕ → ℕ
-- f ≤ g = (n : ℕ) → f n ≤ g n

-- H : (ℕ → ℕ) → (ℕ → ℕ)
-- f ≤ g → H f ≤ H g
-- f mono → H f mono

-- (f ∘ g) x = f (g x)

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

func : (A : Ty) → ⟦ A ⟧T → Set
cat : (A : Ty) → Cat ⟦ A ⟧T

func set _ = ⊤
func (A ⇒ B) F =
  ((a : ⟦ A ⟧T) → func A a → func B (F a) )
  × Func (cat A) (cat B) F

cat set = record { Hom = λ X Y → X → Y ;
                   _∘_ = λ f g x → f (g x) ;
                   ass = refl }
cat (A ⇒ B) = record { Hom = {!!} ; _∘_ = {!!} ; ass = {!!} }
  -- can't do it
  where open Cat (cat A) renaming (_∘_ to _∘A_)
        open Cat (cat B) renaming (_∘_ to _∘B_)  


{-

mono : (A : Ty) → ⟦ A ⟧T → Set
order : (A : Ty) → ⟦ A ⟧T → ⟦ A ⟧T → Set
pre :  (A : Ty) → Pre ⟦ A ⟧T (order A)

mono nat _ = ⊤
mono (A ⇒ B) f =
  ((a : ⟦ A ⟧T) → mono A a → mono B (f a) )
  × ((a b : ⟦ A ⟧T) → order A a b → order B (f a) (f b))

order nat m n = m ≤ n
order (A ⇒ B) f g = (a : ⟦ A ⟧T) → order B (f a) (g a) 

pre nat = record { rfl = {!!} ; trns = {!!} }
pre (A ⇒ B) = record { rfl = λ a → rfl ; trns = λ xy yz a → trns (xy a) (yz a) }
  where open Pre (pre B)
-}
