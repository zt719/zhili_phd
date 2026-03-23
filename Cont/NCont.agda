module NCont where

open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin

open import Function.Base

variable
  I J : Set
  A B C : I → Set
  m n : ℕ

infixr 0 _→*_
_→*_ : (A B : I → Set) → Set
_→*_ {I} A B = (i : I) → A i → B i

id* : A →* A
id* i a = a

_∘*_ : B →* C → A →* B → A →* C
(f ∘* g) = λ i a → f i (g i a)
{-# INLINE _∘*_ #-}

infixr 0 _→2*_
_→2*_ : {I J : Set} (A B : I → J → Set) → Set
_→2*_ {I} {J} A B = (i : I) (j : J) → A i j → B i j

record NCont (n : ℕ) : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Fin n → Set

variable
  SP TQ : NCont n

record _→ᶜ_ (M N : NCont n) : Set where
  constructor _◃_
  open NCont M
  open NCont N renaming (S to T; P to Q)
  field
    fS : S → T
    fP : Q ∘ fS →2* P

record ⟦_⟧ (SP : NCont n) (X : Fin n → Set) : Set where
  constructor _,_
  open NCont SP
  field
    s : S
    f : P s →* X

⟦_⟧₁ : (SP : NCont n) {X Y : Fin n → Set} (f : X →* Y) 
  → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ S ◃ P ⟧₁ g (s , f) = s , g ∘* f

⟦_⟧₂ : SP →ᶜ TQ → (X : Fin n → Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ fS ◃ fP ⟧₂ X (s , f) = fS s , f ∘* fP s
