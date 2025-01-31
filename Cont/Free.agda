{-# OPTIONS --cubical #-}
module Cont.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
  renaming (Iso to _≅_)
open import Function.Base

open import Data.Pullback
open import Cont.Cont

data Free (FC : Cont) (A : Set) : Set where
  Var : A → Free FC A
  Con  : ⟦ FC ⟧ (Free FC A) → Free FC A

variable X Y Z : Set

Free₁ : (FC : Cont) → (X → Y) → Free FC X → Free FC Y
Free₁ (S ◃ P) f (Var x) = Var (f x)
Free₁ (S ◃ P) f (Con (s , p)) = Con (s , (λ x → Free₁ (S ◃ P) f (p x)))
-- Con (⟦ S ◃ P ⟧₁ (Free₁ (S ◃ P) f) (s , p))

{-
module _ (FC : Cont) where


  {-# TERMINATING #-}
  Free₁ : (X → Y) → Free FC X → Free FC Y
  Free₁ f (Var a) = Var (f a)
  Free₁ f (Con op) = {!!} -- Con (⟦ FC ⟧₁ (Free₁ f) op)

  Free₁id : Free₁ (id {A = X}) ≡ id
  Free₁id i (Var a) = Var a
  Free₁id i (Con (s , p)) = Con (s , λ x → Free₁id i (p x))

  Free₁∘ : (f : Y → Z) (g : X → Y) → Free₁ (f ∘ g) ≡ Free₁ f ∘ Free₁ g
  Free₁∘ f g i (Var a) = Var (f (g a))
  Free₁∘ f g i (Con (s , p)) = Con (s , λ x → Free₁∘ f g i (p x))
  
  η : (X : Set) → X → Free FC X
  η _ = Var

  {-# TERMINATING #-}
  μ : (X : Set) → Free FC (Free FC X) → Free FC X
  μ _ (Var a) = a
  μ _ (Con op) = Con (⟦ FC ⟧₁ (μ _) op)

  idl : μ X ∘ η (Free FC X) ≡ id
  idl = refl

  idr : μ X ∘ Free₁ (η X) ≡ id
  idr i (Var a) = Var a
  idr i (Con (s , p)) = Con (s , (λ x → idr i (p x)))

  {-# TERMINATING #-}
  ass : μ X ∘ μ (Free FC X) ≡ μ X ∘ Free₁ (μ X)
  ass i (Var a) = μ _ a
  ass i (Con op) = Con (⟦ FC ⟧₁ (ass i) op)

  module _ {X Y : Set} {f : X → Y} where
    
    φη : X → Pullback (Free₁ f) (η Y)
    φη x = η _ x , f x , refl

    φη⁻ : Pullback (Free₁ f) (η Y) → X
    φη⁻ (Var x , y , eq) = x
    φη⁻ (Con c , y , eq) = _

    φ-iso : X ≅ Pullback (Free₁ f) (η Y)
    φ-iso ._≅_.fun = φη
    φ-iso ._≅_.inv = φη⁻
    φ-iso ._≅_.rightInv = {!!}
    φ-iso ._≅_.leftInv a = refl


  FreeC : Cont
  FreeC = Bool ◃ λ{ false → Unit ; true → ⟦ FC ⟧ Unit }

  Free' : Set → Set
  Free' = ⟦ FreeC ⟧

  Var' : {X : Set} → X → Free' X
  Var' x = false , λ{ tt → x }

  Con' : {X : Set} → ⟦ FC ⟧ (Free' X) → Free' X
  Con' con = true , λ{ (s , p) → {!!} }
-}


data FreeS (FC : Cont) : Set where
  Var : FreeS FC
  Con : ⟦ FC ⟧ (FreeS FC) → FreeS FC

FreeP : (FC : Cont) → FreeS FC → Set
FreeP FC Var = Unit
FreeP (S ◃ P) (Con (s , p)) = Σ[ q ∈ P s ] FreeP (S ◃ P) (p q)
-- S ◃ P   Σ s : S . P s → FreeS (S ◃ P)


FreeC : Cont → Cont
FreeC FC = FreeS FC ◃ FreeP FC
