{-# OPTIONS --guardedness #-}

module Cont.ICont where

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding (J; [_])

variable
  X Y Z : Set
  I J K : Set
  A B C : I → Set

_→*_ : (A B : I → Set) → Set
_→*_ {I} A B = (i : I) → A i → B i

id* : A →* A
id* i a = a

_∘*_ : B →* C → A →* B → A →* C
(f ∘* g) = λ i a → f i (g i a)
{-# INLINE _∘*_ #-}

IJFunc : Set → Set → Set₁
IJFunc I J = Σ[ F ∈ ((I → Set) → J → Set) ] (∀ {A B} → A →* B → F A →* F B)

record IJCont (I J : Set) : Set₁ where
  constructor _◃_
  field
    S : J → Set
    P : (j : J) → S j → I → Set

variable SP : IJCont I J

I⟦_⟧ : IJCont I J → (I → Set) → J → Set
I⟦ S ◃ P ⟧ A j = Σ[ s ∈ S j ] (P j s →* A)

data IW (SP : IJCont I I) : I → Set where
  Isup : I⟦ SP ⟧ (IW SP) →* IW SP

module Fin-IW where

  open import Data.Nat

  variable n : ℕ
  
  S : ℕ → Set
  S n = (Σ[ m ∈ ℕ ] (n ≡ suc m)) × Bool

  P : (n : ℕ) → S n → ℕ → Set
  P zero ()
  P (suc n) ((m , _) , b) k = k ≡ m × b ≡ true

  Fin' : ℕ → Set
  Fin' = IW (S ◃ P)

  zero' : Fin' (suc n)
  zero' {n} = Isup (suc n) (((n , refl) , false) , λ{ i () })

  suc' : Fin' n → Fin' (suc n)
  suc' {n} finn = Isup (suc n) ((({!!} , {!!}) , true) , {!!})

{-
  to : (n : ℕ) → Fin n → Fin' n
  to (suc n) zero = {!!}
  to (suc n) (suc x) = {!!}
-}
