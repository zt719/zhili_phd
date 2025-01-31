{-# OPTIONS --type-in-type --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Function.Base

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

⟦_⟧ : Ty → Set
⟦_⟧F : (A : Ty) → Set
⟦_⟧H : (A : Ty) → ⟦ A ⟧F → ⟦ A ⟧F → Set

⟦ set ⟧ = Set
⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

⟦ set ⟧F = Set
⟦ A ⇒ B ⟧F = {!!}

⟦ set ⟧H X Y = X → Y
⟦ A ⇒ B ⟧H = {!!}
