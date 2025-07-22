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
  open 1Cont F
  field
    s : S
    k : P s → X

1⟦_⟧₁ : (F : 1Cont)
  → {X Y : Set} → (X → Y)
  → 1⟦ F ⟧ X → 1⟦ F ⟧ Y
1⟦ F ⟧₁ f record { s = s ; k = k }
  = record { s = s ; k = f ∘ k }

1⟦_⟧Hom : {SP TQ : 1Cont} (fg : 1ContHom SP TQ)
  → (X : Set) → 1⟦ SP ⟧ X → 1⟦ TQ ⟧ X
1⟦ record { f = f ; g = g } ⟧Hom X record { s = s ; k = k }
  = record { s = f s ; k = k ∘ g s }

record 2Cont : Set₁ where
  inductive
  eta-equality  
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

record 2ContHom (H J : 2Cont) : Set where
  inductive
  eta-equality
  open 2Cont
  field
    f : H .S → J .S
    gx : (s : H .S) → J .PX (f s) → H .PX s
    gf : (s : H .S) → J .PF (f s) → H .PF s
    hf : (s : H .S) (qf : J .PF (f s)) → 2ContHom (H .RF s (gf s qf)) (J .RF (f s) qf) 

record 2⟦_⟧ (H : 2Cont) (F : 1Cont) (X : Set) : Set where
  inductive
  eta-equality
  open 2Cont
  field
    s : H .S
    kx : H .PX s → X
    kf : (p : H .PF s) → 1⟦ F ⟧ (2⟦ H .RF s p ⟧ F X)

{-# TERMINATING #-}
2⟦_⟧₁ : (H : 2Cont)
  → {F G : 1Cont} → 1ContHom F G
  → {X Y : Set} → (X → Y)
  → 2⟦ H ⟧ F X → 2⟦ H ⟧ G Y
2⟦ H ⟧₁ {F} {G} α {X} {Y} f record { s = s ; kf = kf ; kx = kx } =
  record
  { s = s
  ; kx = f ∘ kx
  ; kf = λ pf → 1⟦ α ⟧Hom (2⟦ H .RF s pf ⟧ G Y) (1⟦ F ⟧₁ (2⟦ H .RF s pf ⟧₁ α f) (kf pf))
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

{- Examples -}

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product

B : (Set → Set) → Set → Set
B F X = X × F (F X)

B-2Cont : 2Cont
B-2Cont = record { S = ⊤ ; PX = λ x → ⊤ ; PF = λ x → ⊤ ; RF = λ s x → FX }
  where
  X : 2Cont
  X = record { S = ⊤ ; PX = λ x → ⊤ ; PF = λ x → ⊥ ; RF = λ s () }
  
  FX : 2Cont
  FX = record { S = ⊤ ; PX = λ x → ⊥ ; PF = λ x → ⊤ ; RF = λ s x → X }
