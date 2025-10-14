{-# OPTIONS --guardedness #-}

module Cont.2Cont2 where

open import Function.Base
open import Cont.Cont

record 2Cont : Set₁ where
  constructor _◃_◃_◃_
  inductive
  eta-equality
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

record 2ContHom (SPR TQL : 2Cont) : Set where
  constructor _◃_◃_◃_
  inductive
  eta-equality
  open 2Cont SPR
  open 2Cont TQL renaming (S to T; PX to QX; PF to QF; RF to LF)
  field
    f : S → T
    gx : (s : S) → QX (f s) → PX s
    gf : (s : S) → QF (f s) → PF s
    hf : (s : S) (qf : QF (f s)) → 2ContHom (RF s (gf s qf)) (LF (f s) qf) 

{-# NO_POSITIVITY_CHECK #-}
record 2⟦_⟧ (SPR : 2Cont) (F : Set → Set) (X : Set) : Set where
  constructor _,_,_
  inductive
  eta-equality
  open 2Cont SPR
  field
    s : S
    kx : PX s → X
    kf : (pf : PF s) → F (2⟦ RF s pf ⟧ F X)

open import Data.Product

{-# TERMINATING #-}
app : 2Cont → Cont → Cont
app (S ◃ PX ◃ PF ◃ RF) TQ
  = (S ◃ PX) ×C (ΣC[ s ∈ S ] ΠC[ pf ∈ PF s ] TQ ∘C app (RF s pf) TQ)

{-# NO_POSITIVITY_CHECK #-}
record 2M (SPPR : 2Cont) (X : Set) : Set where
  coinductive
  field
    inf : 2⟦ SPPR ⟧ (2M SPPR) X

{-# NO_POSITIVITY_CHECK #-}
data 2W (SPPR : 2Cont) (X : Set) : Set where
  sup : 2⟦ SPPR ⟧ (2W SPPR) X → 2W SPPR X

{-
  X   →   ℕ∞      X   →      M S P       
  ↓       ↓       ↓            ↓
1 + X → 1 + ℕ∞  1 + X → ⟦ S ◃ P ⟧ (M S P)

 F  →  Bush     F  →      2M SPPR
 ↓      ↓       ↓            ↓ 
H F → H Bush   H F → 2⟦ SPPR ⟧ (2M SPPR)
-}

H : (Set → Set) → Set → Set
H F X = X × F (F X)

open import Data.Unit

SPPR : 2Cont
SPPR = ⊤ ◃ {!!} ◃ {!!} ◃ {!!}
  where
  
