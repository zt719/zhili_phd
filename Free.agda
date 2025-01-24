{-# OPTIONS --cubical #-}

module Free where

open import Function.Base
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cont

open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Bool

data Free (SP : Cont) (A : Set) : Set where
  Var : A → Free SP A
  Op  : ⟦ SP ⟧ (Free SP A) → Free SP A

module _ (SP : Cont) where

  variable A B C : Set

  {-# TERMINATING #-}
  Free₁ : (A → B) → Free SP A → Free SP B
  Free₁ f (Var a) = Var (f a)
  Free₁ f (Op op) = Op (⟦ SP ⟧₁ (Free₁ f) op)

  Free-id : Free₁ (id {A = A}) ≡ id 
  Free-id i (Var a) = Var a
  Free-id i (Op (s , p)) = Op (s , λ x → Free-id i (p x))

  Free-∘ : (f : B → C) (g : A → B) → Free₁ (f ∘ g) ≡ Free₁ f ∘ Free₁ g
  Free-∘ f g i (Var a) = Var (f (g a))
  Free-∘ f g i (Op (s , p)) = Op (s , λ x → Free-∘ f g i (p x))
  
  Free-η : A → Free SP A
  Free-η = Var

  {-# TERMINATING #-}
  Free-μ : Free SP (Free SP A) → Free SP A
  Free-μ (Var a) = a
  Free-μ (Op op) = Op (⟦ SP ⟧₁ Free-μ op)

  Free-idl : Free-μ ∘ Free-η ≡ id {A = Free SP A}
  Free-idl = refl

  Free-idr : Free-μ ∘ Free₁ Free-η ≡ id {A = Free SP A}
  Free-idr i (Var a) = Var a
  Free-idr i (Op (s , p)) = Op (s , (λ x → Free-idr i (p x)))

  {-# TERMINATING #-}
  Free-ass : Free-μ ∘ Free-μ ≡ Free-μ ∘ Free₁ (Free-μ {Cont.S SP})
  Free-ass i (Var a) = Free-μ a
  Free-ass i (Op op) = Op (⟦ SP ⟧₁ (Free-ass i) op)

MC : Cont
MC = Bool ◁ λ{ false → ⊥ ; true → Unit }

Maybe : Set → Set
Maybe = ⟦ MC ⟧

Nothing : {A : Set} → Maybe A
Nothing = false , λ ()

Just : {A : Set} → A → Maybe A
Just a = true , λ{ tt → a }

Maybe₁ :{A B : Set} → (A → B) → Maybe A → Maybe B
Maybe₁ = ⟦ MC ⟧₁
