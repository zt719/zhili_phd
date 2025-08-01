module Cont.2Cont where

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

record 2⟦_⟧₀ (SPR : 2Cont) (F : Cont) (X : Set) : Set where
  constructor _,_,_
  inductive
  eta-equality
  open 2Cont SPR
  field
    s : S
    kx : PX s → X
    kf : (pf : PF s) → ⟦ F ⟧₀ (2⟦ RF s pf ⟧₀ F X)

{-# TERMINATING #-}
2⟦_⟧₁ : (SPR : 2Cont)
  → {F G : Cont} → ContHom F G
  → {X Y : Set} → (X → Y)
  → 2⟦ SPR ⟧₀ F X → 2⟦ SPR ⟧₀ G Y
2⟦ SPR ⟧₁ {F} {G} α {X} {Y} f (s , kx , kf) = s , (f ∘ kx)
   , (λ pf → ⟦ α ⟧Hom (2⟦ RF s pf ⟧₀ G Y) (⟦ F ⟧₁ (2⟦ RF s pf ⟧₁ α f) (kf pf)))
  where open 2Cont SPR

{-# TERMINATING #-}
2⟦_⟧Hom : {H J : 2Cont} → 2ContHom H J
  → (F : Cont) (X : Set)
  → 2⟦ H ⟧₀ F X → 2⟦ J ⟧₀ F X
2⟦ f ◃ gx ◃ gf ◃ hf ⟧Hom F X (s , kx , kf) = f s , (kx ∘ gx s)
  , (λ pf → ⟦ F ⟧₁ (2⟦ hf s pf ⟧Hom F X) (kf (gf s pf)))

open import Data.Product

{-# TERMINATING #-}
2app : 2Cont → Cont → Cont
2app (S ◃ PX ◃ PF ◃ RF) TQ
  = (S ◃ PX) ×C (ΣC[ s ∈ S ] ΠC[ pf ∈ PF s ] TQ ∘C 2app (RF s pf) TQ)

{-
2⟦ S ◃ PX ◃ PF ◃ RF ⟧₀ (T ◃ Q) X
= Σ s : S . (PX s → X) × ((p : PF s) → ⟦ T ◃ Q ⟧₀ (2⟦ RF s pf ⟧₀ (T ◃ Q) X))
= Σ s : S . (PX s → X) × ((p : PF s) → Σ t : T . Q t → 2⟦ RF s pf ⟧₀ (T ◃ Q) X)
...

= (S ◃ PX) ×C ((p : PF s) → (T ◃ Q) ∘C ⟦ RF s pf ⟧ (T ◃ Q)) X
-}

variable
  F₀ G₀ : Set → Set
