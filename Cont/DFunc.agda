{-# OPTIONS --type-in-type #-}

open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

data CTy : Set
data CCon : Set

data CTy where
  _⇒set : CCon → CTy

data CCon where
  ∙ : CCon
  _▹_ : CCon → CTy → CCon

s : CTy
s = ∙ ⇒set

s→s : CTy
s→s = (∙ ▹ s) ⇒set

s→[s→s] : CTy
s→[s→s] = ((∙ ▹ s) ▹ s) ⇒set

[s→s]→s : CTy
[s→s]→s = (∙ ▹ s→s) ⇒set

[s→s]→[s→s] : CTy
[s→s]→[s→s] = ((∙ ▹ s) ▹ s→s) ⇒set


