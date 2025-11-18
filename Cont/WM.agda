{-# OPTIONS --guardedness #-}

module Cont.WM where

open import Cont.Cont
open import Function.Base
open import Relation.Binary.PropositionalEquality

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

W₁ : SP →ᶜ TQ → W SP → W TQ
W₁ (g ◃ h) (sup (s , f)) = sup (g s , λ q → W₁ (g ◃ h) (f (h s q)))

module _ (X : Set) (α : ⟦ SP ⟧ X → X) where

  foldW : W SP → X
  foldW (sup (s , f)) = α (s , (foldW ∘ f))

  commuteW : (sf : ⟦ SP ⟧ (W SP)) → foldW (sup sf) ≡ α (⟦ SP ⟧₁ foldW sf)
  commuteW sf = refl

  !fold : (foldW' : W SP → X)
    (commuteW' : (sf : ⟦ SP ⟧ (W SP)) → foldW' (sup sf) ≡ α (⟦ SP ⟧₁ foldW' sf)) → 
    (w : W SP) → foldW' w ≡ foldW w
  !fold foldW' commuteW' (sup (s , f))
    = trans (commuteW' (s , f)) (cong α (⟦⟧≡ refl λ p → !fold foldW' commuteW' (f p)))

recW : {S : Set} {P : S → Set}
  → (Q : W (S ◃ P) → Set)
  → (((s , f) : ⟦ S ◃ P ⟧ (W (S ◃ P))) → ((p : P s) → Q (f p)) → Q (sup (s , f)))
  → (w : W (S ◃ P)) → Q w
recW Q m (sup (s , f)) = m (s , f) (recW Q m ∘ f)

record M (SP : Cont) : Set where
  coinductive
  field
    inf : ⟦ SP ⟧ (M SP)
open M    

M₁ : SP →ᶜ TQ → M SP → M TQ
inf (M₁ (g ◃ h) msp) with inf msp
... | s , f = g s , λ q → M₁ (g ◃ h) (f (h s q))
