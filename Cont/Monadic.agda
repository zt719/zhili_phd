module Cont.Monadic where

open import Function.Base

open import Cont.Cont

open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality

pullback
  : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
  → (f : A → C) (g : B → C) → Set (ℓ ⊔ ℓ' ⊔ ℓ'')
pullback f g =  Σ[ a ∈ _ ] Σ[ b ∈ _ ] (f a ≡ g b)

{- h : X → Y

              ⟦ f ◃ g ⟧ X
  ⟦ S ◃ P ⟧ X    →      ⟦ T ◃ Q ⟧ X


   ↓ ⟦ S ◃ P ⟧ h          ↓ ⟦ T ◃ Q ⟧ h

              ⟦ f ◃ g ⟧ Y
  ⟦ S ◃ P ⟧ Y    →      ⟦ T ◃ Q ⟧ Y
-}

record MCont : Set₁ where

module _ 
  (S : Set)
  (P : S → Set)
  (T : Set)
  (Q : T → Set)
  (f : S → T)
  (g : (s : S) → Q (f s) → P s)
  where

  φ : {X Y : Set} (k : X → Y)
    → ⟦ S ◃ P ⟧ X → pullback (⟦ T ◃ Q ⟧₁ k) (⟦ f ◃ g ⟧Hom Y)
  φ k (s , p) = (f s , p ∘ g s) , (s , k ∘ p) , refl

{-
  module _
    {g⁻ : (s : S) → P s → Q (f s)}
    {g∘g⁻ : (s : S) → g s ∘ g⁻ s ≡ id}
    {g⁻∘g : (s : S) → g⁻ s ∘ g s ≡ id}  
    where

    φ⁻ : {X Y : Set} (k : X → Y)
      → pullback (⟦ T ◃ Q ⟧₁ k) (⟦ f ◃ g ⟧Hom Y)
      → ⟦ S ◃ P ⟧ X
    φ⁻ k ((t , q) , (s , p) , eq) .⟦_⟧.s = s
    φ⁻ k ((t , q) , (s , p) , eq) .⟦_⟧.k = q ∘ transport (cong Q (sym eq-s)) ∘ g⁻ s 
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
    g⁻ s ps = (φ⁻ (g s) ((f s , id) , (s , id) , refl)) .⟦_⟧.k {!!} --ps
-}
