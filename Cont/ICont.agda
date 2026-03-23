{-# OPTIONS --guardedness #-}

module Cont.ICont where

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum
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

{-
record JFunc (J : Set) : Set₁ where
  constructor _,_
  field
    F : J → Set → Set
    F₁ : (j : J) → (X → Y) → F j X → F j X
    {- +rules -}    
-}

data Finn : ℕ → Set where
  zero : (n : ℕ) → Finn (suc n)
  suc  : (n : ℕ) → Finn n → Finn (suc n)

Func : Set₁
Func = Σ[ F ∈ (Set → Set) ] (∀ {X Y} → (X → Y) → F X → F Y)

Alg : Func → Set₁
Alg (F , _) = Σ[ X ∈ Set ] (F X → X)

{-
IFunc : Set → Set₁
IFunc I = I → Func

ICont : Set → Set₁
ICont I = I → Cont

I⟦_⟧ : ICont I → I → Set → Set
I⟦ SP ⟧ i = ⟦ SP i ⟧

I⟦_⟧₁ : (SP : ICont I) (i : I) → (X → Y) → I⟦ SP ⟧ i X → I⟦ SP ⟧ i Y
I⟦ SP ⟧₁ i = ⟦ SP i ⟧₁

data IW (SP : ICont I) : I → Set where
  Isup : (i : I) → I⟦ SP ⟧ i (IW SP i) → IW SP i


variable n : ℕ

FinCont : ICont ℕ
FinCont zero = ⊥ᶜ
FinCont (suc n) = ⊤ᶜ ⊎ᶜ FinCont n
  
Fin' : ℕ → Set
Fin' = IW FinCont

zero' : Fin' (suc n)
zero' {n} = Isup (suc n) (inj₁ tt , λ ())

suc' : Fin' n → Fin' (suc n)
suc' {n} (Isup n (s , f)) = Isup (suc n) (inj₂ s , suc' ∘ f)

to : Fin n → Fin' n
to zero = zero'
to (suc i) = suc' (to i)
-}

FinSig : I → Set → Set
FinSig = {!!}

IFunc : Set → Set₁
IFunc I = Σ[ F ∈ ((I → Set) → I → Set) ] (∀ {A B} → A →* B → F A →* F B)

record ICont (I : Set) : Set₁ where
  constructor _◃_
  field
    S : I → Set
    P : (i : I) → S i → Set

variable SP : ICont I

I⟦_⟧ : ICont I → (I → Set) → I → Set
I⟦ S ◃ P ⟧ A i = Σ[ s ∈ S i ] (P i s → A i)

data IW (SP : ICont I) : I → Set where
  Isup : I⟦ SP ⟧ (IW SP) →* IW SP

open import Codata.Musical.Notation using (♭; ∞; ♯_)

data Coℕ : Set where
  zero : Coℕ
  suc  : (n : ∞ Coℕ) → Coℕ

infinity : Coℕ
infinity = suc (♯ infinity)

data _≈_ : Coℕ → Coℕ → Set where
  zero : zero ≈ zero
  suc  : ∀ {m n} → ∞ (♭ m ≈ ♭ n) → suc m ≈ suc n

data IM (SP : ICont I) : I → Set where
  Isup : I⟦ SP ⟧ (λ i → ∞ (IM SP i)) →* IM SP

Isup⁻ : IM SP →* I⟦ SP ⟧ (IM SP)
Isup⁻ _ (Isup i (s , f)) = s , λ p → ♭ (f p)

unfoldIM : A →* I⟦ SP ⟧ A → A →* IM SP
unfoldIM α i x with α i x
... | s , f = Isup i (s , λ i' → ♯ unfoldIM α i (f i'))
