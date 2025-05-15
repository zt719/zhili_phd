{-# OPTIONS --cubical #-}

module Cont.2Cont2 where

open import Function.Base

infix  0 _◃_
record 1Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

record 1ContHom (SP TQ : 1Cont) : Set where
  constructor _◃_
  open 1Cont SP
  open 1Cont TQ renaming (S to T; P to Q)
  field
    f : S → T
    g : (s : S) → Q (f s) → P s

record 1⟦_⟧ (SP : 1Cont) (X : Set) : Set where
  constructor _,_
  open 1Cont SP
  field
    s : S
    k : P s → X

1⟦_⟧₁ : (SP : 1Cont) {X Y : Set} → (X → Y) → 1⟦ SP ⟧ X → 1⟦ SP ⟧ Y
1⟦ SP ⟧₁ f (s , k) = s , (f ∘ k)

1⟦_⟧Hom : {SP TQ : 1Cont} (fg : 1ContHom SP TQ)
  → (X : Set) → 1⟦ SP ⟧ X → 1⟦ TQ ⟧ X
1⟦ f ◃ g ⟧Hom X (s , k) = f s , (k ∘ g s)

{-# NO_POSITIVITY_CHECK #-}
record 2Cont : Set₁ where
  constructor _◃_◃_◃_
  inductive
  eta-equality  
  field
    S : Set
    P₀ : S → Set
    R₀ : (s : S) → P₀ s → 2Cont
    P₁ : S → Set

record 2ContHom (SPRP TQLQ : 2Cont) : Set where
  constructor _◃_◃_◃_
  inductive
  eta-equality
  open 2Cont SPRP
  open 2Cont TQLQ renaming (S to T; P₀ to Q₀; R₀ to L₀; P₁ to Q₁)
  field
    f : S → T
    g₀ : (s : S) → Q₀ (f s) → P₀ s
    h₀ : (s : S) (q₀ : Q₀ (f s)) → 2ContHom (R₀ s (g₀ s q₀)) (L₀ (f s) q₀) 
    g₁ : (s : S) → Q₁ (f s) → P₁ s

hhh : 2Cont → 1Cont → 1Cont
hhh (2S ◃ P₀ ◃ R₀ ◃ P₁) (S ◃ P) = {!!} ◃ {!!}
