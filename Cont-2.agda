{-# OPTIONS --guardedness --cubical #-}

module Cont-2 where

open import Cubical.Data.Equality
open import Function.Base
  using (_∘_)

record hSet : Type₁ where
  field
    ∣_∣ : Type
    isSet : (x y : ∣_∣) → x ≡ y
open hSet    

infix  0 _◁_

record Cont : Type₁ where
  constructor _◁_
  field
    S : hSet
    P : ∣ S ∣ → hSet

record _-C→_ (SP TQ : Cont) : Type where
  constructor _◁_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    u : ∣ S ∣ → ∣ T ∣
    f : (s : ∣ S ∣) → ∣ Q (u s) ∣ → ∣ P s ∣

idCont : {SP : Cont} → SP -C→ SP
idCont = id ◁ λ s → id

∘Cont : {SP TQ WR : Cont} → SP -C→ TQ → TQ -C→ WR → SP -C→ WR
∘Cont (u ◁ f) (v ◁ g)  = v ∘ u ◁ λ s → f s ∘ g (u s)

record ⟦_⟧ (SP : Cont) (X : Type) : Type where
  constructor _,_
  open Cont SP
  field
    s : ∣ S ∣
    p : ∣ P s ∣ → X

⟦_⟧₁ : (SP : Cont) {X Y : Type}
  → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ S ◁ P ⟧₁ f (s , g) = s , f ∘ g

⟦id⟧ : (SP : Cont) {X : Type}
  → ⟦ SP ⟧₁ {X} id ≡ id
⟦id⟧ (S ◁ P) = refl

⟦∘⟧ : (SP : Cont) {X Y Z : Type} (f : Y → Z) (g : X → Y)
  → ⟦ SP ⟧₁ f ∘ ⟦ SP ⟧₁ g ≡ ⟦ SP ⟧₁ (f ∘ g)
⟦∘⟧ (S ◁ P) f g = refl

⟦_⟧₂ : {SP TQ : Cont} → SP -C→ TQ
   → (X : Type) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ u ◁ f ⟧₂ _ (s , h) = u s , h ∘ f s

⟦nat⟧ : {SP TQ : Cont} (uf : SP -C→ TQ) {X Y : Type} (g : X → Y)
  → ⟦ TQ ⟧₁ g ∘ ⟦ uf ⟧₂ X ≡ ⟦ uf ⟧₂ Y ∘ ⟦ SP ⟧₁ g
⟦nat⟧ (u ◁ f) g = refl

from : {SP TQ : Cont}
  → ((X : Type) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X)
  → SP -C→ TQ
from {S ◁ P} {T ◁ Q} α = s ∘ m ◁ p ∘ m
  where
  open ⟦_⟧
  m : (s : ∣ S ∣) → ⟦ T ◁ Q ⟧ ∣ P s ∣
  m s = α ∣ P s ∣ (s , id)

