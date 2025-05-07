{-# OPTIONS --cubical --type-in-type --guardedness #-}

module tlca01a where

open import Cubical.Foundations.Prelude
open import Function.Base

Alg : (T : Set → Set) → Set
Alg T = Σ[ X ∈ Set ] (T X → X)

private
  variable
    A B : Set

module Nat where

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
    
  record Stream (A : Set) : Set where
    coinductive
    field
      head : A
      tail : Stream A
  open Stream

  ψ : (ℕ → B) → Stream B
  ψ f .head = f zero
  ψ f .tail = ψ (f ∘ suc)
  
  φ : Stream B → ℕ → B
  φ bs zero = bs .head
  φ bs (suc n) = φ (bs .tail) n


module List where

  infixr 5 _∷_
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  record BadTree (A B : Set) : Set where
    coinductive
    field
      label : B
      branches : A → BadTree A B
  open BadTree    
  
  ψ : (List A → B) → BadTree A B
  ψ f .label = f []
  ψ f .branches a = ψ (f ∘ (a ∷_))

  φ : BadTree A B → List A → B
  φ bt [] = bt .label
  φ bt (a ∷ as) = φ (bt .branches a) as


module BTree where

  data BTree (A : Set) : Set where
    leaf : BTree A
    node : BTree A → BTree A → BTree A

  record Bush (A : Set) : Set where
    coinductive
    field
      head : A
      tail : Bush (Bush A)
  open Bush

  {-# TERMINATING #-}
  ψ : {A B : Set} → (BTree A → B) → Bush B
  ψ f .head = f leaf
  ψ f .tail = ψ (λ t → ψ (λ u → f (node t u)))

  φ : {A B : Set} → Bush B → BTree A → B
  φ bb leaf = bb .head
  φ bb (node t u) = φ (φ (bb .tail) t) u


module FTree where

  data FTree (X Y : Set) : Set where
    leaf : FTree X Y
    node : X → Y → FTree X Y
