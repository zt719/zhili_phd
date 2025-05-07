{-# OPTIONS --cubical-compatible #-}

open import Data.Unit
open import Data.Nat
open import Data.List

data RoseTree : Set where
  node : List RoseTree → RoseTree

{-
r : RoseTree
r = node (node [] ∷ (node (node [] ∷ [])) ∷ node (node [] ∷ (node (node [] ∷ [])) ∷ []) ∷ [])
-}

open import Data.Nat

countNodes : RoseTree → ℕ
countNodes (node ts) = suc (countListNodes ts)
  where
  countListNodes : List RoseTree → ℕ
  countListNodes [] = 0
  countListNodes (t ∷ ts) = countNodes t + countListNodes ts


NRoseTree : ℕ → Set
NRoseTree zero = ⊤
NRoseTree (suc n) = List (NRoseTree n)

countNRoseTree : {n : ℕ} → NRoseTree n → ℕ
countNRoseTree {zero} tt = zero
countNRoseTree {suc n} ts = countListNRoseTree ts
  where
  countListNRoseTree : List (NRoseTree n) → ℕ
  countListNRoseTree [] = zero
  countListNRoseTree (t ∷ ts) = countNRoseTree t + countListNRoseTree ts
