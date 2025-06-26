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
  = record { s = s ; k = f ∘ k }

1⟦_⟧Hom : {SP TQ : 1Cont} (fg : 1ContHom SP TQ)
  → (X : Set) → 1⟦ SP ⟧ X → 1⟦ TQ ⟧ X
1⟦ record { f = f ; g = g } ⟧Hom X record { s = s ; k = k }
  = record { s = f s ; k = k ∘ g s }

{-# NO_POSITIVITY_CHECK #-}
record 2Cont : Set₁ where
  inductive
  eta-equality  
  field
    S : Set
    Px : S → Set
    Pf : S → Set
    Rf : (s : S) → Pf s → 2Cont

record 2ContHom (H J : 2Cont) : Set where
  inductive
  eta-equality
  open 2Cont
  field
    f : H .S → J .S
    gx : (s : H .S) → J .Px (f s) → H .Px s
    gf : (s : H .S) → J .Pf (f s) → H .Pf s
    hf : (s : H .S) (qf : J .Pf (f s)) → 2ContHom (H .Rf s (gf s qf)) (J .Rf (f s) qf) 

{-# NO_POSITIVITY_CHECK #-}
record 2⟦_⟧ (H : 2Cont) (F : 1Cont) (X : Set) : Set where
  inductive
  eta-equality
  open 2Cont
  field
    s : H .S
    kx : H .Px s → X
    kf : (p : H .Pf s) → 1⟦ F ⟧ (2⟦ H .Rf s p ⟧ F X)

{-# TERMINATING #-}
2⟦_⟧₁ : (H : 2Cont)
  → {F G : 1Cont} → 1ContHom F G
  → {X Y : Set} → (X → Y)
  → 2⟦ H ⟧ F X → 2⟦ H ⟧ G Y
2⟦ H ⟧₁ {F} {G} α {X} {Y} f record { s = s ; kf = kf ; kx = kx } =
  record
  { s = s
  ; kx = f ∘ kx
  ; kf = λ pf → 1⟦ α ⟧Hom (2⟦ H. Rf s pf ⟧ G Y) (1⟦ F ⟧₁ (2⟦ H .Rf s pf ⟧₁ α f) (kf pf))  
  }
  where open 2Cont

{-# TERMINATING #-}
2⟦_⟧Hom : {H J : 2Cont} → 2ContHom H J
  → (F : 1Cont) (X : Set)
  → 2⟦ H ⟧ F X → 2⟦ J ⟧ F X
2⟦ record { f = f ; gf = gf ; hf = hf ; gx = gx } ⟧Hom F X
  record { s = s ; kf = kf ; kx = kx } = record
  { s = f s
  ; kx = kx ∘ gx s
  ; kf = λ pf → 1⟦ F ⟧₁ (2⟦ hf s pf ⟧Hom F X) (kf (gf s pf))  
  }
