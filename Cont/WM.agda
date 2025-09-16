{-# OPTIONS --guardedness #-}

module Cont.WM where

open import Cont.Cont
open import Function.Base

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

rec : {S : Set} {P : S → Set}
  → (Q : W (S ◃ P) → Set)
  → ((s : S) (k : P s → W (S ◃ P)) → ((p : P s) → Q (k p)) → Q (sup (s , k)))
  → (x : W (S ◃ P)) → Q x
rec Q m (sup (s , k)) = m s k (λ p → rec Q m (k p))

record M (SP : Cont) : Set where
  coinductive
  field
    inf : ⟦ SP ⟧ (M SP)
