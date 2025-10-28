{-# OPTIONS --guardedness #-}

module Cont.WM where

open import Cont.Cont
open import Function.Base

recW : {S : Set} {P : S → Set}
  → (Q : W (S ◃ P) → Set)
  → ((s : S) (k : P s → W (S ◃ P)) → ((p : P s) → Q (k p)) → Q (sup (s , k)))
  → (x : W (S ◃ P)) → Q x
recW Q m (sup (s , k)) = m s k (λ p → recW Q m (k p))

W₁ : {SP TQ : Cont} (fg : SP →ᶜ TQ) → W SP → W TQ
W₁ (f ◃ g) (sup (s , k)) = sup (f s , λ q → W₁ (f ◃ g) (k (g s q)) )

{-
M₁ : {SP TQ : Cont} (fg : Hom SP TQ) → M SP → M TQ
inf (M₁ (f ◃ g) m) with inf m
... | s , k = f s , λ q → M₁ (f ◃ g) (k (g s q))
-}
