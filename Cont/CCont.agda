{-# OPTIONS --cubical --guardedness #-}

module Cont.CCont where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets

Cat = Category (ℓ-suc ℓ-zero) ℓ-zero

Func : Cat → Cat → Type (ℓ-suc ℓ-zero)
Func = Functor {ℓ-suc ℓ-zero} {ℓ-zero}

Sets : Cat
Sets = SET ℓ-zero

{- Categorical Container -}

record Cont : Type (ℓ-suc (ℓ-suc ℓ-zero)) where
  constructor _◃_
  field
    S : Cat
    P : Func S Sets

variable SP TQ : Cont

record ContHom (SP TQ : Cont) : Type (ℓ-suc ℓ-zero) where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    F : Func S T
    δ : NatTrans (Q ∘F F) P

ContHom-id : ContHom SP SP
ContHom-id {S ◃ P} = 𝟙⟨ S ⟩ ◃ {!!}
    

{-
module _ (ℂ : Cat) where

  open Cat ℂ

  infix  0 _◃_
  record Cont : Type₁ where
    constructor _◃_
    field
      S : Type
      P : S → Obj

  private variable SP TQ : Cont

  record ContHom (SP TQ : Cont) : Type where
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

  record ⟦_⟧ (SP : Cont) (X : Obj) : Type where
    constructor _,_
    open Cont SP
    field
      s : S
      k : Hom (P s) X

  ⟦_⟧₁ : (SP : Cont) {X Y : Obj} → Hom X Y → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
  ⟦ SP ⟧₁ f (s , k) = s , (f ∘ k)

  ⟦_⟧Hom : {SP TQ : Cont} → ContHom SP TQ → (X : Obj) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
  ⟦ f ◃ g ⟧Hom X (s , k) = f s , (k ∘ g s)
-}
