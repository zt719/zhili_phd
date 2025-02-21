{-# OPTIONS --cubical #-}

open import Function.Base
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

B : (Set → Set) → Set → Set
B F X = X × F (F X)

BB : {F G : Set → Set}
  → {F₁ : {X Y : Set} → (X → Y) → (F X → F Y)}
  → Σ[ B₁ ∈ (({X : Set} → F X → G X) → ({X : Set} → B F X → B G X)) ]
  {!!} × {!!}
-- B₁ {F₁ = F₁} α (x , ffx) = x , α (F₁ α ffx)

Bto : (F : Set → Set)
  → Σ[ F₁ ∈ ({X Y : Set} → (X → Y) → (F X → F Y)) ]
  ({X : Set} → F₁ (id {A = X}) ≡ id)
  × ({X Y Z : Set} (f : Y → Z) (g : X → Y) → F₁ (f ∘ g) ≡ F₁ f ∘ F₁ g)
  → Σ[ BF₁ ∈ ({X Y : Set} → (X → Y) → (B F X → B F Y)) ]
  (({X : Set} → BF₁ (id {A = X}) ≡ id)
  × ({X Y Z : Set} (f : Y → Z) (g : X → Y) → BF₁ (f ∘ g) ≡ BF₁ f ∘ BF₁ g))
Bto F (F₁ , F-id , F-∘) =
  (λ f (x , ffx) → f x , F₁ (F₁ f) ffx)
  , (λ i (x , ffx) → x , (cong F₁ F-id ∙ F-id) i ffx)
  , (λ f g i (x , ffx) → f (g x) , (cong F₁ (F-∘ f g) ∙ F-∘ (F₁ f) (F₁ g)) i ffx)
