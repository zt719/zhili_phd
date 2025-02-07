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
open import Cont.Id

private
  variable
    X Y Z R : Set

{-
data Reader (R X : Set) : Set where
  runReader : (R → X) → Reader R X

-}

ReaderC : Set → Cont
ReaderC R = R ◃ λ r → ⊥
