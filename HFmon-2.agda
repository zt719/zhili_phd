{-# OPTIONS --type-in-type #-}

{- tree types, with dom and appT -}

open import Data.Product
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Nat

{- Syntax -}

data Ty : Set where
  nat : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

⟦_⟧T : Ty → Set
⟦ nat ⟧T = ℕ
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

-- f : ℕ → ℕ
-- mono f = m ≤ n → f m ≤ f n

-- f g : ℕ → ℕ
-- f ≤ g = (n : ℕ) → f n ≤ g n

-- H : (ℕ → ℕ) → (ℕ → ℕ)
-- f ≤ g → H f ≤ H g
-- f mono → H f mono

record Pre (X : Set)(R : X → X → Set) : Set where
  field
    rfl : {x : X} → R x x
    trns : {x y z : X} → R x y → R y z → R x z

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
