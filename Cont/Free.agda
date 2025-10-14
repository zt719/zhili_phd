{-# OPTIONS --cubical --guardedness #-}

module Cont.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Function.Base

open import Cont.Cont

data Free (SP : Cont) (A : Set) : Set where
  Var : A → Free SP A
  Con : ⟦ SP ⟧₀ (Free SP A) → Free SP A

private
  variable
    X Y Z : Set

module _ (SP : Cont) where

  Free₁ : (X → Y) → Free SP X → Free SP Y
  Free₁ f (Var x) = Var (f x)
  Free₁ f (Con k) = Con (⟦ SP ⟧₁ (Free₁ f) k)
  
  Free-id : Free₁ (id {A = X}) ≡ id
  Free-id i (Var x) = Var x
  Free-id i (Con (s , p)) = Con (s , Free-id i ∘ p)

  Free₁∘ : (f : Y → Z) (g : X → Y) → Free₁ (f ∘ g) ≡ Free₁ f ∘ Free₁ g
  Free₁∘ f g i (Var x) = Var (f (g x))
  Free₁∘ f g i (Con (s , p)) = Con (s , Free₁∘ f g i ∘ p )
  
  η : (X : Set) → X → Free SP X
  η X x = Var x

  μ : (X : Set) → Free SP (Free SP X) → Free SP X
  μ X (Var x) = x
  μ X (Con (s , p)) = Con (s , μ X ∘ p)

  idl : μ X ∘ η (Free SP X) ≡ id
  idl = refl

  idr : μ X ∘ Free₁ (η X) ≡ id
  idr i (Var x) = Var x
  idr i (Con (s , p)) = Con (s , idr i ∘ p)

  xss : μ X ∘ μ (Free SP X) ≡ μ X ∘ Free₁ (μ X)
  xss i (Var x) = μ _ x
  xss i (Con (s , p)) = Con (s , xss i ∘ p)

  module _ {X Y : Set} {f : X → Y} where
    
    φη : X → Pullback (Free₁ f) (η Y)
    φη x = η _ x , f x , refl

    φη⁻ : Pullback (Free₁ f) (η Y) → X
    φη⁻ (Var x , y , eq) = x
    φη⁻ (Con c , y , eq) = _

data FreeS (SP : Cont) : Set where
  Var : FreeS SP
  Con : ⟦ SP ⟧₀ (FreeS SP) → FreeS SP

FreeP : (SP : Cont) → FreeS SP → Set
FreeP SP Var = ⊤
FreeP (S ◃ P) (Con (s , p)) = Σ[ q ∈ P s ] FreeP (S ◃ P) (p q)

FreeC : Cont → Cont
FreeC SP = FreeS SP ◃ FreeP SP
