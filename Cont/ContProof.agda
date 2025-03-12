{-# OPTIONS --cubical #-}

module Cont.ContProof where

open import Cubical.Foundations.Prelude
open import Cont.Cont
open import Function.Base

-- Functor & Natural Transformation

record Func : Set₁ where
  field
    F₀ : Set → Set
    F₁ : ∀ {X Y} → (X → Y) → F₀ X → F₀ Y
    F-id : ∀ {X} → F₁ {X} id ≡ id
    F-∘ : ∀ {X Y Z} (f : Y → Z) (g : X → Y)
        → F₁ (f ∘ g) ≡ F₁ f ∘ F₁ g

record Nat (F G : Func) : Set₁ where
  open Func F
  open Func G renaming (F₀ to G₀; F₁ to G₁)
  field
    η : ∀ X → F₀ X → G₀ X
    nat : ∀ {X Y} (f : X → Y) → G₁ f ∘ η X ≡ η Y ∘ F₁ f

postulate
  Nat≡ : {F G : Func} {α β : Nat F G}
    → Nat.η α ≡ Nat.η β → α ≡ β

private variable SP TQ : Cont

C→F : Cont → Func
C→F SP = record
  { F₀ = ⟦ SP ⟧
  ; F₁ = ⟦ SP ⟧₁
  ; F-id = refl
  ; F-∘ = λ f g → refl
  }

CH→N : Cont[ SP , TQ ] → Nat (C→F SP) (C→F TQ)
CH→N uf = record
  { η = ⟦ uf ⟧₂
  ; nat = λ f → refl
  }

-- ⟦_⟧ is fully-faithfull
module _ {α : Nat (C→F SP) (C→F TQ)} where
  open Nat α
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  open ⟦_⟧

  N→CH : Nat (C→F SP) (C→F TQ) → Cont[ SP , TQ ]
  N→CH α = s ∘ m ◃ p ∘ m
    where
      m : (s : S) → ⟦ T ◃ Q ⟧ (P s)
      m s = η (P s) (s , id)

  uf′ : Cont[ SP , TQ ]
  uf′ = N→CH α

  path : CH→N uf′ ≡ α
  path = Nat≡ (λ i X (s , f) → nat f i (s , id))

_∘c_ : Cont → Cont → Cont
(S ◃ P) ∘c (T ◃ Q) =
  Σ[ s ∈ S ] (P s → T) ◃ λ (s , f) → Σ[ p ∈ P s ] Q (f p)
{-
  ⟦ S ◃ P ⟧ (⟦ T ◃ Q ⟧ X)
= Σ[ s ∈ S ] (P s → Σ[ t ∈ T ] (Q t → X))
= Σ[ s ∈ S ] Σ[ f ∈ (P s → T) ] (p : P s) → Q (f p) → X
= Σ[ sf ∈ Σ[ s ∈ S ] (P s → T) ] (p : P (fst sf)) → Q ((snd sf) p) → X
= Σ[ sf ∈ Σ[ s ∈ S ] (P s → T) ] (Σ[ p ∈ P (fst sf)) ] (Q ((snd sf) p)) → X)
= ⟦ Σ[ s ∈ S ] (P s → T) ◃ λ sf → Σ[ p ∈ P (fst sf) ] (Q (snd sf) p) ⟧ X
= ⟦ Σ[ s ∈ S ] (P s → T) ◃ λ (s , f) → Σ[ p ∈ P s ] (Q f p) ⟧ X
-}

