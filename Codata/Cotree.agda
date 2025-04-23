{-# OPTIONS --guardedness #-}

module Codata.Cotree where

record Cotree (A : Set) : Set where
  coinductive
  field
    value : A
    left  : Cotree A
    right : Cotree A
