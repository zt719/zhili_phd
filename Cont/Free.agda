{-# OPTIONS --guardedness #-}

module Cont.Free where

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Function.Base
open import Relation.Binary.PropositionalEquality

open import Cont.Cont

data Free (SP : Cont) (A : Set) : Set where
  var : A → Free SP A
  con : ⟦ SP ⟧ (Free SP A) → Free SP A

variable X Y Z : Set

Free₁ : (X → Y) → Free SP X → Free SP Y
Free₁ f (var x) = var (f x)
Free₁ {SP = SP} f (con k) = con (⟦ SP ⟧₁ (Free₁ f) k)

{-
  Free-id : Free₁ (id {A = X}) ≡ id
  Free-id i (var x) = var x
  Free-id i (con (s , p)) = con (s , Free-id i ∘ p)

  Free₁∘ : (f : Y → Z) (g : X → Y) → Free₁ (f ∘ g) ≡ Free₁ f ∘ Free₁ g
  Free₁∘ f g i (var x) = var (f (g x))
  Free₁∘ f g i (con (s , p)) = con (s , Free₁∘ f g i ∘ p )
-}

{-
  η : (X : Set) → X → Free SP X
  η X x = var x

  μ : (X : Set) → Free SP (Free SP X) → Free SP X
  μ X (var x) = x
  μ X (con (s , p)) = con (s , μ X ∘ p)

  idl : μ X ∘ η (Free SP X) ≡ id
  idl = refl
-}
{-
  idr : μ X ∘ Free₁ (η X) ≡ id
  idr i (var x) = var x
  idr i (con (s , p)) = con (s , idr i ∘ p)

  xss : μ X ∘ μ (Free SP X) ≡ μ X ∘ Free₁ (μ X)
  xss i (var x) = μ _ x
  xss i (con (s , p)) = con (s , xss i ∘ p)
-}

data FreeS (SP : Cont) : Set where
  var : FreeS SP
  con : ⟦ SP ⟧ (FreeS SP) → FreeS SP

FreeP : (SP : Cont) → FreeS SP → Set
FreeP SP var = ⊤
FreeP (S ◃ P) (con (s , f)) = Σ[ p ∈ P s ] FreeP (S ◃ P) (f p)

Freeᶜ : Cont → Cont
Freeᶜ SP = FreeS SP ◃ FreeP SP
