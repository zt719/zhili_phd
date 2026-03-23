module Cont.HContTel where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

{- Ty & Tel -}

data Ty : Set

data Tel : Set

data Ty where
  _⇒* : Tel → Ty

variable A B C : Ty

infixr 5 _◃_
data Tel where
  •   : Tel
  _◃_ : Ty → Tel → Tel

_ : Ty
_ = • ⇒*
