{-# OPTIONS --type-in-type --cubical-compatible #-}

module Cont.CCont where

record Cat : Set where
  field
    Obj : Set
    Hom : Obj → Obj → Set
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    {- +laws -}

id' : {X : Set} → X → X
id' x = x

_∘'_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(f ∘' g) x = f (g x)

module _ (ℂ : Cat) where

  open Cat ℂ

  infix  0 _◃_
  record Cont : Set₁ where
    constructor _◃_
    field
      S : Set
      P : S → Obj

  private variable SP TQ : Cont

  record ContHom (SP TQ : Cont) : Set where
    constructor _◃_
    open Cont SP
    open Cont TQ renaming (S to T; P to Q)
    field
      f : S → T
      g : (s : S) → Hom (Q (f s)) (P s)

  CONT : Cat
  CONT .Obj = Cont
  CONT .Hom = ContHom
  CONT .id = id' ◃ λ s → id
  CONT ._∘_ (f ◃ g) (h ◃ k) = f ∘' h ◃ λ s → k s ∘ g (h s)

  record ⟦_⟧ (SP : Cont) (X : Obj) : Set where
    constructor _,_
    open Cont SP
    field
      s : S
      k : Hom (P s) X

  ⟦_⟧₁ : (SP : Cont) {X Y : Obj} → Hom X Y → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
  ⟦ SP ⟧₁ f (s , k) = s , (f ∘ k)

  ⟦_⟧Hom : {SP TQ : Cont} → ContHom SP TQ → (X : Obj) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
  ⟦ f ◃ g ⟧Hom X (s , k) = f s , (k ∘ g s)
