{-# OPTIONS --type-in-type #-}

module Cont.2Cont where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Function.Base

record Cat : Set where
  field
    Obj : Set
    Hom : Obj → Obj → Set

  Fam : Set
  Fam = Σ[ I ∈ Set ] (I → Obj)

  FamHom : Fam → Fam → Set
  FamHom (I , F) (J , G) =
    Σ[ f ∈ (I → J) ] ((i : I) → Hom (F i) (G (f i)))
    
open Cat

record 2Cont : Set

record 2ContHom (C D : 2Cont) : Set

2CONT : Cat
2CONT .Obj = 2Cont
2CONT .Hom = 2ContHom

record 2Cont where
  inductive
  field
    S : Set
    P : S → Set
    PR : S → Fam 2CONT
    -- P₀ : S → Set
    -- R₀ : (s : S) → P s → 2Cont

record 2ContHom C D where
  inductive
  eta-equality
  open 2Cont
  field
    f : C .S → D .S
    g : (s : C .S) → D .P (f s) → C .P s
    h : (s : C .S) → FamHom 2CONT (D .PR (f s)) (C .PR s)
open 2ContHom

{-# TERMINATING #-}
idHom : ∀ {X} → 2ContHom X X
idHom .2ContHom.f = id
idHom .2ContHom.g s = id
idHom .2ContHom.h s = id , λ i → idHom

{-# TERMINATING #-}
_∘Hom_ : ∀ {X Y Z} → 2ContHom Y Z → 2ContHom X Y → 2ContHom X Z
(δ ∘Hom γ) .f = δ .f ∘ γ .f
(δ ∘Hom γ) .g s = γ .g s ∘ δ .g (γ .f s)
(δ ∘Hom γ) .h s =
  γ .h s .proj₁ ∘ δ .h (γ .f s) .proj₁
  , λ i → {!_∘Hom_!}

{-# NO_POSITIVITY_CHECK #-}
record ⟦_⟧ (C : 2Cont) (F : Set → Set) (X : Set) : Set where
  inductive
  eta-equality
  open 2Cont C
  field
    s : S
    p : P s → X
    k : (p₀ : PR s .proj₁) → F (⟦ PR s .proj₂ p₀ ⟧ F X)

⟦_⟧₁ : {C D : 2Cont} (δ : 2ContHom C D) →
  (F : Set → Set) (X : Set) → ⟦ C ⟧ F X → ⟦ D ⟧ F X
⟦ record { f = f ; g = g ; h = h } ⟧₁ F X
  record { s = s ; p = p ; k = k } =
  record { s = f s ; p = p ∘ g s ; k = {!!} }
