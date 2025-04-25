{-# OPTIONS --type-in-type #-}

module Cont.2Cont1 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Function.Base

record Cat : Set where
  field
    Obj : Set
    Hom : Obj → Obj → Set
    ID : ∀ {X} → Hom X X
    COM : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    {- +laws -}

{-
  FAM : Cat
  FAM .Obj = Σ[ I ∈ Set ] (I → Obj)
  FAM .Hom (I , F) (J , G) =
    Σ[ f ∈ (I → J) ] ((i : I) → Hom (F i) (G (f i)))
  FAM .ID = id , λ i → ID
  FAM .COM (f , α) (g , β) = f ∘ g , λ i → COM (α (g i)) (β i)
-}

  FAM⁻ : Cat
  FAM⁻ .Obj = Σ[ I ∈ Set ] (I → Obj)
  FAM⁻ .Hom (I , F) (J , G) = Σ[ f ∈ (I → J) ] ((i : I) → Hom (G (f i)) (F i))
  FAM⁻ .ID = id , λ i → ID
  FAM⁻ .COM (f , α) (g ,  β) = f ∘ g , λ i → COM (β i) (α (g i))
open Cat

record 2Cont : Set

record 2ContHom (C D : 2Cont) : Set

2CONT : Cat

{-# NO_POSITIVITY_CHECK #-}
record 2Cont where
  inductive
  field
    S : Set
    PR₀ : S → FAM⁻ 2CONT .Obj
    P₁ : S → Set    

record 2ContHom C D where
  inductive
  eta-equality
  open 2Cont
  field
    f : C .S → D .S
    g₀ : (s : C .S) → FAM⁻ 2CONT .Hom (D .PR₀ (f s)) (C .PR₀ s)
    g₁ : (s : C .S) → D .P₁ (f s) → C .P₁ s
    
open 2ContHom

{-# TERMINATING #-}
2CONT .Obj = 2Cont
2CONT .Hom = 2ContHom
2CONT .ID .f = id
2CONT .ID .g₁ s = id
2CONT .ID .g₀ s = id , λ i → 2CONT .ID
2CONT .COM δ γ .f = δ .f ∘ γ .f
2CONT .COM δ γ .g₁ s = γ .g₁ s ∘ δ .g₁ (γ .f s)
2CONT .COM δ γ .g₀ s = (γ .g₀ s .proj₁ ∘ δ .g₀ (γ .f s) .proj₁)
  , λ i → 2CONT .COM (δ .g₀ (γ .f s) .proj₂ i) (γ .g₀ s .proj₂ (δ .g₀ (γ .f s) .proj₁ i))

{-# NO_POSITIVITY_CHECK #-}
record ⟦_⟧ (C : 2Cont) (F : Set → Set) (X : Set) : Set where
  inductive
  eta-equality
  open 2Cont C
  field
    s : S
    k : (p₀ : PR₀ s .proj₁) → F (⟦ PR₀ s .proj₂ p₀ ⟧ F X)
    l : P₁ s → X

{-# TERMINATING #-}
⟦_⟧₂ : {C D : 2Cont} (δ : 2ContHom C D) →
  (F : Set → Set) (F₁ : ∀ {X Y} → (X → Y) → F X → F Y) (X : Set) → ⟦ C ⟧ F X → ⟦ D ⟧ F X
⟦ record { f = f ; g₀ = g₀ ; g₁ = g₁ } ⟧₂ F F₁ X
  record { s = s ; k = k ; l = l } = record
  { s = f s
  ; k = λ p₀ → F₁ (⟦ g₀ s .proj₂ p₀ ⟧₂ F F₁ X) (k (g₀ s .proj₁ p₀))
  ; l = l ∘ g₁ s
  }
