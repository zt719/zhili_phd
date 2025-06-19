module Cont.2Cont where

open import Function.Base

record 1Cont : Set₁ where
  field
    S : Set
    P : S → Set

record 1ContHom (F G : 1Cont) : Set where
  open 1Cont
  field
    f : F .S → G .S
    g : (s : F .S) → G .P (f s) → F .P s

record 1⟦_⟧ (F : 1Cont) (X : Set) : Set where
  open 1Cont
  field
    s : F .S
    k : F .P s → X

1⟦_⟧₁ : (F : 1Cont)
  → {X Y : Set} → (X → Y)
  → 1⟦ F ⟧ X → 1⟦ F ⟧ Y
1⟦ F ⟧₁ f record { s = s ; k = k }
  = record { s = s ; k = λ z → f (k z) }

1⟦_⟧Hom : {SP TQ : 1Cont} (fg : 1ContHom SP TQ)
  → (X : Set) → 1⟦ SP ⟧ X → 1⟦ TQ ⟧ X
1⟦ record { f = f ; g = g } ⟧Hom X record { s = s ; k = k }
  = record { s = f s ; k = λ p → k (g s p) }

{-# NO_POSITIVITY_CHECK #-}
record 2Cont : Set₁ where
  inductive
  eta-equality  
  field
    S : Set
    P₀ : S → Set
    R₀ : (s : S) → P₀ s → 2Cont
    P₁ : S → Set

record 2ContHom (H J : 2Cont) : Set where
  inductive
  eta-equality
  open 2Cont
  field
    f : H .S → J .S
    g₀ : (s : H .S) → J .P₀ (f s) → H .P₀ s
    h₀ : (s : H .S) (q₀ : J .P₀ (f s)) → 2ContHom (H .R₀ s (g₀ s q₀)) (J .R₀ (f s) q₀) 
    g₁ : (s : H .S) → J .P₁ (f s) → H .P₁ s

{-# NO_POSITIVITY_CHECK #-}
record 2⟦_⟧ (H : 2Cont) (F : 1Cont) (X : Set) : Set where
  inductive
  eta-equality
  open 2Cont
  field
    s : H .S
    k₀ : (p : H .P₀ s) → 1⟦ F ⟧ (2⟦ H .R₀ s p ⟧ F X)
    k₁ : H .P₁ s → X

{-# TERMINATING #-}
2⟦_⟧₁ : (H : 2Cont)
  → {F G : 1Cont} → 1ContHom F G
  → {X Y : Set} → (X → Y)
  → 2⟦ H ⟧ F X → 2⟦ H ⟧ G Y
2⟦ H ⟧₁ {F} {G} α {X} {Y} f record { s = s ; k₀ = k₀ ; k₁ = k₁ } =
  record
  { s = s
  ; k₀ = λ p₀ → 1⟦ α ⟧Hom (2⟦ H. R₀ s p₀ ⟧ G Y) (1⟦ F ⟧₁ (2⟦ H .R₀ s p₀ ⟧₁ α f) (k₀ p₀))
  ; k₁ = f ∘ k₁
  }
  where open 2Cont

{-# TERMINATING #-}
2⟦_⟧Hom : {H J : 2Cont} → 2ContHom H J
  → (F : 1Cont) (X : Set)
  → 2⟦ H ⟧ F X → 2⟦ J ⟧ F X
2⟦ record { f = f ; g₀ = g₀ ; h₀ = h₀ ; g₁ = g₁ } ⟧Hom F X
  record { s = s ; k₀ = k₀ ; k₁ = k₁ } = record
  { s = f s
  ; k₀ = λ p₀ → 1⟦ F ⟧₁ (2⟦ h₀ s p₀ ⟧Hom F X) (k₀ (g₀ s p₀))
  ; k₁ = k₁ ∘ g₁ s
  }

app : 2Cont → 1Cont → 1Cont
app record { S = S ; P₀ = P₀ ; R₀ = R₀ ; P₁ = P₁ } record { S = 1S ; P = 1P }
  = record { S = {!!} ; P = {!!} }


_ : {H : 2Cont} {F : 1Cont} {X : Set} → 2⟦ H ⟧ F X → 1⟦ app H F ⟧ X
_ = {!!}


