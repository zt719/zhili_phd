{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

{- Pointed Type & Loop Space -}

record Pointed : Type₁ where
  constructor _,_
  field
    A : Type
    a : A

Ω : ℕ → Pointed → Pointed
Ω zero (A , a) = A , a
Ω (suc n) (A , a) = Ω n ((a ≡ a) , refl)
