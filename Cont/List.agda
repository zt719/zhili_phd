{-# OPTIONS --cubical #-}
module Cont.List where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Data.Fin
open import Cubical.Foundations.Isomorphism
  renaming (Iso to _≅_)
open import Function.Base

open import Data.Pullback
open import Cont.Cont

open import Cubical.Data.List

fmap : {X Y : Set} → (X → Y) → List X → List Y
fmap f [] = []
fmap f (x ∷ xs) = f x ∷ fmap f xs

η : (X : Set) → X → List X
η _ x = x ∷ []

μ : (X : Set) → List (List X) → List X
μ _ [] = []
μ _ (xs ∷ xss) = xs ++ μ _ xss

module _ {X Y : Set} {f : X → Y} where

  φη : X → Pullback (fmap f) (η Y)
  φη x = η _ x , f x , refl

  φη⁻ : Pullback (fmap f) (η Y) → X
  φη⁻ ([] , y , eq) = _
  φη⁻ (x ∷ [] , y , eq) = x
  φη⁻ (x ∷ _ ∷ _ , y , eq) = _

  φη-iso : X ≅ Pullback (fmap f) (η Y)
  φη-iso ._≅_.fun = φη
  φη-iso ._≅_.inv = φη⁻
  φη-iso ._≅_.rightInv = _
  φη-iso ._≅_.leftInv a = refl

  -- lem : ∀ {xs ys} → fmap f (xs ++ ys) ≡ fmap f xs ++ fmap f ys
  -- lem = {!!}

  φμ : List (List X) → Pullback (fmap f) (μ Y)
  φμ xss = μ _ xss , (fmap (fmap f) xss) , _

  φμ⁻ : Pullback (fmap f) (μ Y) → List (List X)
  φμ⁻ ([] , yss , eq) = _
  φμ⁻ (x ∷ xs , yss , eq) = _

IdC : Cont
IdC = Unit ◃ λ{ tt → Unit }

Id' : Set → Set
Id' = ⟦ IdC ⟧

ListC : Cont
ListC = ℕ ◃ Fin

List' : Set → Set
List' = ⟦ ListC ⟧

fmap' : {X Y : Set} → (X → Y) → List' X → List' Y
fmap' = ⟦ ListC ⟧₁

ηC : Cont[ IdC , ListC ]
ηC = (λ{ tt → suc zero }) ◃ λ{ tt zero → tt }

η'' : (X : Set) → Id' X → List' X
η'' = ⟦ ηC ⟧₂

η' : (X : Set) → X → List' X
η' _ x = η'' _ (tt , λ{ tt → x })

module _ where

  open Cont[_,_] ηC
  open Cont IdC
  open Cont ListC renaming (S to T; P to Q)

  f⁻ : (s : S) → P s → Q (u s)
  f⁻ tt tt = zero

  f-iso : (s : S) → Q (u s) ≅ P s
  f-iso s ._≅_.fun = f s
  f-iso s ._≅_.inv = f⁻ s
  f-iso s ._≅_.rightInv tt i = tt
  f-iso s ._≅_.leftInv zero i = zero

-- μC : Cont[ ListC ∘c ListC , ListC ]
-- μC = {!!} ◃ {!!}
