{-# OPTIONS --cubical-compatible #-}

module Cont.Cont where

open import Function.Base

{- Container -}
infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

private variable SP TQ WR : Cont

{- Container Hom -}
record ContHom (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    f : S → T
    g : (s : S) → Q (f s) → P s

{- Container Extension Functor -}
record ⟦_⟧ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    k : P s → X

⟦_⟧₁ : (SP : Cont) {X Y : Set} → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ f sk = sk .s , (f ∘ sk .k)
  where open ⟦_⟧
{-# INLINE ⟦_⟧₁ #-}

⟦_⟧₁' : (SP : Cont) {X Y : Set} → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁' f (s , k) = s , (f ∘ k)

⟦_⟧Hom : {SP TQ : Cont} (fg : ContHom SP TQ)
  → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ f ◃ g ⟧Hom X (s , k) = f s , (k ∘ g s)

open import Data.Product
open import Data.Sum

_×C_ : Cont → Cont → Cont
(S ◃ P) ×C (T ◃ Q) = S × T ◃ λ (s , t) → P s ⊎ Q t

{-
  ⟦ S ◃ P ⟧ X × ⟦ T ◃ Q ⟧ X
= (Σ s : S . P s → X) × Σ t : T . Q t → X) -- definition
≃ Σ s : S . Σ t : T . (P s → X) × (Q t → X) -- comm
≃ Σ s : S . Σ t : T . P s ⊎ Q t → X -- distr
≃ Σ (s , t) : S × T . P s ⊎ Q t → X -- assoc
= ⟦ S × T ◃ λ (s , t) → P s ⊎ Q t ⟧ X -- definition
-}

_⊎C_ : Cont → Cont → Cont
(S ◃ P) ⊎C (T ◃ Q) = S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t }

{-
  ⟦ S ◃ P ⟧ X ⊎ ⟦ T ◃ Q ⟧ X
= (Σ s : S . P s → X) ⊎ Σ t : T . Q t → X) -- definition

≃ Σ[ x : S ⊎ T ] case x P Q
= ⟦ S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t } ⟧ X --definition


-}

_∘C_ : Cont → Cont → Cont
(S ◃ P) ∘C (T ◃ Q) = (Σ[ s ∈ S ] (P s → T)) ◃ λ (s , f) → Σ[ p ∈ P s ] Q (f p)

{-
  ⟦ S ◃ P ⟧ ∘ ⟦ T ◃ Q ⟧ X
= ⟦ S ◃ P ⟧ (⟦ T ◃ Q ⟧ X)
= Σ s : S . (P s → Σ t : T . (Q t → X))  --definition
≃ Σ s : S . Σ f : P s → T . ((p : P s) → Q (f p) → X)  -- choice
≃ Σ (s , f) : (Σ s : S . P s → T) . ((p : P s) → Q (f p) → X) -- unassoc
≃ Σ (s , f) : (Σ s : S . P s → T) . Σ p : P s . Q (f p) → X -- uncurry
= ⟦ Σ s : S . P s → T ◃ λ (s , f) → Σ p : P s . Q (f p) ⟧ X -- definition
-}

ΣC : {I : Set} → (I → Cont) → Cont
ΣC {I} C⃗ = Σ[ i ∈ I ] C⃗ i .S ◃ λ (i , s) → C⃗ i .P s
  where open Cont

{-
  Σ i : I . ⟦ C i ⟧ X
≃ Σ i : I . ⟦ S i ◃ P i ⟧ X -- rewrite
= Σ i : I . Σ s : S i . (P i s → X) -- definition
≃ Σ (i , s) : Σ I S . (P i s → X) -- unassoc
= ⟦ Σ I S ◃ λ (i , s) → P i s ⟧ X -- definition
-}

ΠC : {I : Set} → (I → Cont) → Cont
ΠC {I} C⃗ = ((i : I) → C⃗ i .S) ◃ λ f → Σ[ i ∈ I ] C⃗ i .P (f i)
  where open Cont

{-
  (i : I) → ⟦ C i ⟧ X
= (i : I) → ⟦ S i ◃ P i ⟧ X -- rewrite
= (i : I) → Σ s : S i . (P i s → X) -- definition
≃ Σ f : (i : I) → S i . ((i : I) → P i (f i) → X) -- choice
≃ Σ f : (i : I) → S i . Σ i : I . P i (f i) → X -- curry
= ⟦ (i : I) → S i ◃ λ f → Σ i : I . P i (f i) ⟧ X -- definition
-}
