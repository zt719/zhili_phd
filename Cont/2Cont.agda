{-# OPTIONS --guardedness #-}

module Cont.2Cont where

open import Cont.Cont

record 2Cont : Set₁ where
  constructor _◃_+_+_
  inductive
  eta-equality
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

record 2ContHom (SPR TQL : 2Cont) : Set where
  constructor _◃_+_+_
  inductive
  eta-equality
  open 2Cont SPR
  open 2Cont TQL renaming (S to T; PX to QX; PF to QF; RF to LF)
  field
    f : S → T
    gx : (s : S) → QX (f s) → PX s
    gf : (s : S) → QF (f s) → PF s
    hf : (s : S) (qf : QF (f s)) → 2ContHom (RF s (gf s qf)) (LF (f s) qf) 

{-
record 2⟦_⟧ (SPR : 2Cont) (F : Cont) (X : Set) : Set where
  constructor _,_,_
  inductive
  eta-equality
  open 2Cont SPR
  field
    s : S
    kx : PX s → X
    kf : (pf : PF s) → ⟦ F ⟧ (2⟦ RF s pf ⟧ F X)

{-# NO_POSITIVITY_CHECK #-}
record 2⟦_⟧' (SPR : 2Cont) (F : Set → Set) (X : Set) : Set where
  --  constructor _+_+_
  inductive
  eta-equality
  open 2Cont SPR
  field
    s : S
    kx : PX s → X
    kf : (pf : PF s) → F (2⟦ RF s pf ⟧' F X)

{-# TERMINATING #-}
2⟦_⟧₁ : (SPR : 2Cont)
  → {F G : Cont} → ContHom F G
  → {X Y : Set} → (X → Y)
  → 2⟦ SPR ⟧ F X → 2⟦ SPR ⟧ G Y
2⟦ SPR ⟧₁ {F} {G} α {X} {Y} f (s , kx , kf) =
  s , (λ px → f (kx px)) , (λ pf → ⟦ α ⟧ContHom (2⟦ RF s pf ⟧ G Y) (⟦ F ⟧₁ (2⟦ RF s pf ⟧₁ α f) (kf pf)))
  where open 2Cont SPR

{-# TERMINATING #-}
2⟦_⟧Hom : {H J : 2Cont} → 2ContHom H J
  → (F : Cont) (X : Set)
  → 2⟦ H ⟧ F X → 2⟦ J ⟧ F X
2⟦ f ◃ gx + gf + hf ⟧Hom F X (s , kx , kf) = f s , (λ px → kx (gx s px)) , (λ pf → ⟦ F ⟧₁ (2⟦ hf s pf ⟧Hom F X) (kf (gf s pf)))
-}

{-# TERMINATING #-}
⟦_⟧' : 2Cont → Cont → Cont
⟦ S ◃ PX + PF + RF ⟧' TQ
  = (S ◃ PX) ×C (ΣC[ s ∈ S ] ΠC[ pf ∈ PF s ] TQ ∘C ⟦ RF s pf ⟧' TQ)

open import Data.Sum
open import Data.Product

{-
{-# TERMINATING #-}
2W : 2Cont → Cont

{-# NO_POSITIVITY_CHECK #-}
record 2WS (H : 2Cont) : Set

{-# TERMINATING #-}
2WP : (H : 2Cont) → 2WS H → Set

record 2WS H where
  inductive
  eta-equality
  open 2Cont H
  open Cont (2W H) renaming (S to T; P to Q)
  field
    sx : S
    sf : S
    h : (pf : PF sf) → Σ[ t ∈ T ] (Q t → (⟦ RF sf pf ⟧' (T ◃ Q)) .Cont.S)

2WP (S ◃ PX + PF + RF) record { sx = sx ; sf = sf ; h = h }
  = PX sx ⊎ Σ[ pf ∈ PF sf ] let (t , f) = h pf in Σ[ q ∈ Q t ] (⟦ RF sf pf ⟧' (T ◃ Q)) .Cont.P (f q)
  where
  open Cont (2W (S ◃ PX + PF + RF)) renaming (S to T; P to Q)

2W SPPR = 2WS SPPR ◃ 2WP SPPR
-}

-- 2sup : {SPPR : 2Cont} → ContHom (⟦ SPPR ⟧' (2W SPPR)) 2W SPPR
-- 2sup = ?
