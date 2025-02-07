{-# OPTIONS --cubical #-}

module Cont.Id where

open import Cubical.Data.Unit
open import Cont.Cont

IdC : Cont
IdC = Unit ◃ λ{ tt → Unit }

Id : Set → Set
Id = ⟦ IdC ⟧
