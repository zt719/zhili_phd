{-# OPTIONS --cubical #-}

module Cont.Monadic where

open import Function.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
  renaming (Iso to _≅_)

open import Cont.Cont
open import Data.Pullback

module _ 
  (S : Set)
  (P : S → Set)
  (T : Set)
  (Q : T → Set)
  (f : S → T)
  (g : (s : S) → Q (f s) → P s)
  where

  φ : {X Y : Set} (k : X → Y)
    → ⟦ S ◃ P ⟧ X
    → Pullback (⟦ T ◃ Q ⟧₁ k) (⟦ f ◃ g ⟧Hom Y)
  φ k (s , p) = (f s , p ∘ g s) , (s , k ∘ p) , refl

  module _
    {g⁻ : (s : S) → P s → Q (f s)}
    {g∘g⁻ : (s : S) → g s ∘ g⁻ s ≡ id}
    {g⁻∘g : (s : S) → g⁻ s ∘ g s ≡ id}  
    where

    φ⁻ : {X Y : Set} (k : X → Y)
      → Pullback (⟦ T ◃ Q ⟧₁ k) (⟦ f ◃ g ⟧Hom Y)
      → ⟦ S ◃ P ⟧ X
    φ⁻ k ((t , q) , (s , p) , eq) .⟦_⟧.s = s
    φ⁻ k ((t , q) , (s , p) , eq) .⟦_⟧.p = q ∘ transport (cong Q (sym eq-s)) ∘ g⁻ s 
      where
        eq-s : t ≡ f s
        eq-s = cong ⟦_⟧.s eq

  φ∘φ⁻ : {X Y : Set} (k : X → Y) → φ k ∘ φ⁻ k ≡ id
  φ∘φ⁻ {X} {Y} k i ((t , q) , (s , p') , eq) = ((eq-s (~ i)) , {!!}) , {!!}
  
    where
      eq-s : t ≡ f s
      eq-s = cong ⟦_⟧.s eq

      -- eq-p : PathP (λ i₁ → Q (eq i₁ .⟦_⟧.s) → Y)
      --  (⟦_⟧.p (⟦ T ◃ Q ⟧₁ k (t , q)))
      --  (⟦_⟧.p (⟦ f ◃ g ⟧₂ Y (s , p')))
      -- eq-p = {!!}

 {-
   φ⁻∘φ : {X Y : Set} (k : X → Y) → φ⁻ k ∘ φ k ≡ id
   φ⁻∘φ k i (s , p) = s , λ ps → {!!}
 -}


  module _
    {φ⁻ : {X Y : Set} (k : X → Y) → Pullback (⟦ T ◃ Q ⟧₁ k) (⟦ f ◃ g ⟧Hom Y) → ⟦ S ◃ P ⟧ X}
    {φ⁻∘φ : {X Y : Set} (k : X → Y) → φ⁻ k ∘ φ k ≡ id}
    {φ∘φ⁻ : {X Y : Set} (k : X → Y) → φ k ∘ φ⁻ k ≡ id}
    where

    g⁻ : (s : S) → P s → Q (f s)
    g⁻ s ps = (φ⁻ (g s) ((f s , id) , (s , id) , refl)) .⟦_⟧.p {!!} --ps
