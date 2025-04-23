{-# OPTIONS --guardedness --cubical-compatible #-}

module Codata.Bush where
  
record Bush (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Bush (Bush A)
