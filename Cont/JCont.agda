module Cont.JCont where

open import Data.Product
open import Function.Base

private variable
  J : Set
  X Y Z : Set

infix  0 _◃_

record JCont (J : Set) : Set₁ where
  constructor _◃_
  field
    S : Set
    P : J → S → Set

private variable
  SP TQ : JCont J

record JContHom (SP TQ : JCont J) : Set where
  constructor _◃_
  open JCont SP
  open JCont TQ renaming (S to T; P to Q)
  field
    f : S → T
    g : (j : J) (s : S) → Q j (f s) → P j s

record ⟦_⟧ (SP : JCont J) (X : Set) (j : J) : Set where
  constructor _,_
  open JCont SP
  field
    s : S
    k : P j s → X

⟦_⟧₁ : (SP : JCont J)
  → (X → Y)
  → (j : J) → ⟦ SP ⟧ X j → ⟦ SP ⟧ Y j
⟦ SP ⟧₁ f j (s , k) = s , f ∘ k

⟦_⟧Hom : (fg : JContHom SP TQ)
  → (j : J) → ⟦ SP ⟧ X j → ⟦ TQ ⟧ X j
⟦ f ◃ g ⟧Hom j (s , k) = f s , k ∘ g j s

data WI (S : Set) (P : J → S → Set) : J → Set where
  sup : (j : J) → ⟦ S ◃ P ⟧ (WI S P j) j → WI S P j
