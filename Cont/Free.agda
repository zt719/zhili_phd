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

private
  variable
    X Y Z : Set

module _ (FC : Cont) where

{-
  {-# TERMINATING #-}
  Free₁ : (X → Y) → Free FC X → Free FC Y
  Free₁ f (Var a) = Var (f a)
  Free₁ f (Con op) = Con (⟦ FC ⟧₁ (Free₁ f) op)
-}

  Free₁ : (X → Y) → Free FC X → Free FC Y
  Free₁ f (Var x) = Var (f x)
  Free₁ f (Con (s , p)) = Con (s , Free₁ f ∘ p)
  
  Free-id : Free₁ (id {A = X}) ≡ id
  Free-id i (Var x) = Var x
  Free-id i (Con (s , p)) = Con (s , Free-id i ∘ p)

  Free₁∘ : (f : Y → Z) (g : X → Y) → Free₁ (f ∘ g) ≡ Free₁ f ∘ Free₁ g
  Free₁∘ f g i (Var x) = Var (f (g x))
  Free₁∘ f g i (Con (s , p)) = Con (s , Free₁∘ f g i ∘ p )
  
  η : (X : Set) → X → Free FC X
  η X x = Var x

  μ : (X : Set) → Free FC (Free FC X) → Free FC X
  μ X (Var x) = x
  μ X (Con (s , p)) = Con (s , μ X ∘ p)

  idl : μ X ∘ η (Free FC X) ≡ id
  idl = refl

  idr : μ X ∘ Free₁ (η X) ≡ id
  idr i (Var x) = Var x
  idr i (Con (s , p)) = Con (s , idr i ∘ p)

  xss : μ X ∘ μ (Free FC X) ≡ μ X ∘ Free₁ (μ X)
  xss i (Var x) = μ _ x
  xss i (Con (s , p)) = Con (s , xss i ∘ p)

  module _ {X Y : Set} {f : X → Y} where
    
    φη : X → Pullback (Free₁ f) (η Y)
    φη x = η _ x , f x , refl

    φη⁻ : Pullback (Free₁ f) (η Y) → X
    φη⁻ (Var x , y , eq) = x
    φη⁻ (Con c , y , eq) = _

{-
    φ-iso : X ≅ Pullbxck (Free₁ f) (η Y)
    φ-iso ._≅_.fun = φη
    φ-iso ._≅_.inv = φη⁻
    φ-iso ._≅_.rightInv = {!!}
    φ-iso ._≅_.leftInv x = refl
-}

data FreeS (FC : Cont) : Set where
  Var : FreeS FC
  Con : ⟦ FC ⟧ (FreeS FC) → FreeS FC

FreeP : (FC : Cont) → FreeS FC → Set
FreeP FC Var = Unit
FreeP (S ◃ P) (Con (s , p)) = Σ[ q ∈ P s ] FreeP (S ◃ P) (p q)

FreeC : Cont → Cont
FreeC FC = FreeS FC ◃ FreeP FC
