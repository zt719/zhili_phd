{-# OPTIONS --cubical #-}
module Cont.Either where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sum renaming (rec to ⊎rec)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
  renaming (Iso to _≅_)
open import Function.Base

open import Data.Pullback
open import Cont.Cont

neq : {A B : Type} {l : A} {r : B} → inl l ≡ inr r → ⊥
neq {A} {B} {l} {r} pf = subst (⊎rec (λ a → A) λ b → ⊥) pf l

module _ (E : Type) where

  M : Type → Type
  M X = X ⊎ E

  M₁ : {X Y : Type} → (X → Y) → M X → M Y
  M₁ f (inl x) = inl (f x)
  M₁ f (inr e) = inr e

  M-id : {X : Type} → M₁ (id {A = X}) ≡ id
  M-id i (inl x) = inl x
  M-id i (inr e) = inr e

  M-∘ : {X Y Z : Type} (f : Y → Z) (g : X → Y)
    → M₁ (f ∘ g) ≡ M₁ f ∘ M₁ g
  M-∘ f g i (inl x) = inl (f (g x))
  M-∘ f g i (inr e) = inr e

  η : (X : Type) → X → M X
  η _ x = inl x

  μ : (X : Type) → M (M X) → M X
  μ _ (inl x+e) = x+e
  μ _ (inr e) = inr e

  idl : {X : Type} → μ X ∘ η (M X) ≡ id
  idl = refl

  idr : {X : Type} → μ X ∘ M₁ (η X) ≡ id
  idr i (inl x) = inl x
  idr i (inr e) = inr e

  ass : {X : Type} → μ X ∘ μ (M X) ≡ μ X ∘ M₁ (μ X)
  ass i (inl x) = μ _ x
  ass i (inr e) = inr e

  module _ {X Y : Type} {f : X → Y} where

    φ : X → Pullback (M₁ f) (η Y)
    φ x = inl x , f x , refl

    φ⁻ : Pullback (M₁ f) (η Y) → X
    φ⁻ (inl x , y , eq) = x
    φ⁻ (inr e , y , eq) = ⊥-elim {A = λ x → X} (neq (sym eq))
    
    φ-isIso : X ≅ Pullback (M₁ f) (η Y)
    φ-isIso ._≅_.fun = φ
    φ-isIso ._≅_.inv = φ⁻
    φ-isIso ._≅_.rightInv = λ
      { (inl x , y , eq) i → inl x , {!!} , {!!}
      ; (inr e , y , eq) i → ⊥-elim
        {A = λ x → {!!}}
        (neq (sym eq))
      }
    φ-isIso ._≅_.leftInv = λ a i → a
  
cont : Type → Cont
cont E = Bool ◃ λ{ false → Unit ; true → Unit }

Either : Type → Type → Type
Either E = ⟦ cont E ⟧

left : {X E : Type} → X → Either E X
left x = false , λ{ tt → x }
