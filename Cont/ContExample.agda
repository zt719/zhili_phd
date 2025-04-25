module Cont.ContExample where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin

open import Function.Base

open import Cont.Cont

variable X Y : Set

{- Maybe -}

PB : Bool → Set
PB false = ⊥
PB true = ⊤

MaybeCont : Cont
MaybeCont = Bool ◃ PB

Maybe : Set → Set
Maybe = ⟦ MaybeCont ⟧

Maybe₁ : (X → Y) → Maybe X → Maybe Y
Maybe₁ = ⟦ MaybeCont ⟧₁

nothing : Maybe X
nothing = false , λ ()

just : X → Maybe X
just x = true , λ{ tt → x }

{- List -}

ListCont : Cont
ListCont = ℕ ◃ Fin

List : Set → Set
List = ⟦ ListCont ⟧

List₁ : (X → Y) → List X → List Y
List₁ = ⟦ ListCont ⟧₁

[] : List X
[] = zero , λ ()

_∷_ : X → List X → List X
x ∷ (s , p) = suc s , λ{ zero → x ; (suc n) → p n }

{- head & tail -}

tailContHom : ContHom ListCont ListCont
tailContHom = f ◃ g
  where
  f : ℕ → ℕ
  f zero = zero
  f (suc n) = n

  g : (n : ℕ) → Fin (f n) → Fin n
  g (suc n) x = suc x

tail : (X : Set) → List X → List X
tail = ⟦ tailContHom ⟧₂

headContHom : ContHom ListCont MaybeCont
headContHom = f ◃ g
  where
  f : ℕ → Bool
  f zero = false
  f (suc n) = true

  g : (n : ℕ) → PB (f n) → Fin n
  g (suc n) tt = zero

head : (X : Set) → List X → Maybe X
head = ⟦ headContHom ⟧₂

{- State -}

open import Data.Product

variable S : Set

StateCont : Set → Cont
StateCont S = (S → S) ◃ λ _ → ⊤ 

State : Set → Set → Set
State S = ⟦ StateCont S ⟧
