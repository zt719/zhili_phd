{-# OPTIONS --cubical #-}
module Cont.Reader where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
  renaming (Iso to _≅_)
open import Function.Base

open import Data.Pullback
open import Cont.Cont

IdC : Cont
IdC = Unit ◃ λ{ tt → Unit }

Id' : Set → Set
Id' = ⟦ IdC ⟧

Reader : Set → Set → Set
Reader R X = R → X

module _ {R : Set} where

  M : Set → Set
  M = Reader R

  fmap : {X Y : Set} → (X → Y) → M X → M Y
  fmap f g = f ∘ g

  η : (X : Set) → X → M X
  η _ x r = x

  μ : (X : Set) → M (M X) → M X
  μ _ mmx r = mmx r r

  module _ {X Y : Set} {f : X → Y} where

    φη : X → Pullback (fmap f) (η Y)
    φη x = η _ x , f x , refl

    -- φη⁻ : Pullback (fmap f) (η Y) → X
    -- φη⁻ (mx , y , eq) = mx {!!}

  MC : Cont
  MC = Unit ◃ λ{ tt → R }

  M' : Set → Set
  M' = ⟦ MC ⟧

  ηC : Cont[ IdC , MC ]
  ηC = (λ{ tt → tt }) ◃ λ{ tt r → tt }

  η'' : (X : Set) → Id' X → M' X
  η'' = ⟦ ηC ⟧₂

  η' : (X : Set) → X → M' X
  η' X x = η'' X (tt , (λ{ tt → x }))

  module _ where

    open Cont[_,_] ηC
    open Cont IdC
    open Cont MC renaming (S to T; P to Q)

    -- f⁻ : (s : S) → P s → Q (u s)
    -- f⁻ tt tt = {!!}
