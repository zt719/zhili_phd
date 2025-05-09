{-# OPTIONS --type-in-type --cubical-compatible #-}

module Cont.1Cont where

open import Cont.CCont

open Cat

SET : Cat
SET .Obj = Set
SET .Hom A B = A → B
SET .id = id'
SET ._∘_ = _∘'_

1Cont : Set
1Cont = Cont SET

1ContHom : 1Cont → 1Cont → Set
1ContHom = ContHom SET

1⟦_⟧ : 1Cont → Set → Set
1⟦_⟧ = ⟦_⟧

1⟦_⟧₁ : (SP : 1Cont) → {X Y : Set} → (X → Y) → 1⟦ SP ⟧ X → 1⟦ SP ⟧ Y
1⟦_⟧₁ = ⟦_⟧₁

1⟦_⟧Hom : ∀ {SP TQ} → 1ContHom SP TQ → ∀ X → 1⟦ SP ⟧ X → 1⟦ TQ ⟧ X
1⟦_⟧Hom = ⟦_⟧Hom
