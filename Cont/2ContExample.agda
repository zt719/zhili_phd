module Cont.2ContExample where

open import Cont.2Cont2 

data C (F : Set → Set) (X : Set) : Set where
  mkC : X → F X → C F X

data D (F : Set → Set) (X : Set) : Set where
  [] : D F X
  _,_∷_ : X → F X → D F X → D F X
