{-# OPTIONS --guardedness #-}

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

record 2⟦_⟧ (SPR : 2Cont) (F : Cont) (X : Set) : Set where
  constructor _,_,_
  inductive
  eta-equality
  open 2Cont SPR
  field
    s : S
    kx : PX s → X
    kf : (pf : PF s) → ⟦ F ⟧ (2⟦ RF s pf ⟧ F X)

{-# TERMINATING #-}
2⟦_⟧₁ : (SPR : 2Cont)
  → {F G : Cont} → ContHom F G
  → {X Y : Set} → (X → Y)
  → 2⟦ SPR ⟧ F X → 2⟦ SPR ⟧ G Y
2⟦ SPR ⟧₁ {F} {G} α {X} {Y} f (s , kx , kf) = s , (f ∘ kx)
   , (λ pf → ⟦ α ⟧ContHom (2⟦ RF s pf ⟧ G Y) (⟦ F ⟧₁ (2⟦ RF s pf ⟧₁ α f) (kf pf)))
  where open 2Cont SPR

{-# TERMINATING #-}
2⟦_⟧Hom : {H J : 2Cont} → 2ContHom H J
  → (F : Cont) (X : Set)
  → 2⟦ H ⟧ F X → 2⟦ J ⟧ F X
2⟦ f ◃ gx ◃ gf ◃ hf ⟧Hom F X (s , kx , kf) = f s , (kx ∘ gx s)
  , (λ pf → ⟦ F ⟧₁ (2⟦ hf s pf ⟧Hom F X) (kf (gf s pf)))

open import Data.Product

{-# TERMINATING #-}
app : 2Cont → Cont → Cont
app (S ◃ PX ◃ PF ◃ RF) TQ
  = (S ◃ PX) ×C (ΣC[ s ∈ S ] ΠC[ pf ∈ PF s ] TQ ∘C app (RF s pf) TQ)

{-
2⟦ S ◃ PX ◃ PF ◃ RF ⟧ (T ◃ Q) X
= Σ s : S . (PX s → X) × ((p : PF s) → ⟦ T ◃ Q ⟧ (2⟦ RF s pf ⟧ (T ◃ Q) X))
= Σ s : S . (PX s → X) × ((p : PF s) → Σ t : T . Q t → 2⟦ RF s pf ⟧ (T ◃ Q) X)
...

= (S ◃ PX) ×C ((p : PF s) → (T ◃ Q) ∘C ⟦ RF s pf ⟧ (T ◃ Q)) X
-}

--app₁ : (SPPR : 2Cont) → ContHom SP TQ → ContHom (app SPPR SP) (app SPPR TQ)
--app₁ = {!!}

open import Data.Unit
open import Data.Sum

variable X Y : Set

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : ⊤ ⊎ ℕ∞
open ℕ∞

Maybe : Set → Set
Maybe X = ⊤ ⊎ X

unfoldℕ∞ : (X → Maybe X) → X → ℕ∞
pred∞ (unfoldℕ∞ α x) with α x
... | inj₁ tt = inj₁ tt
... | inj₂ x' = inj₂ (unfoldℕ∞ α x')

record Bush (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Bush (Bush A)
open Bush

{-# TERMINATING #-}
Bush₁ : (X → Y) → Bush X → Bush Y
head (Bush₁ f bx) = f (head bx)
tail (Bush₁ f bx) = Bush₁ (Bush₁ f) (tail bx)

{-
unfold𝔹ush : 𝔽 ⇒ ℍ 𝔽 → 𝔽 ⇒ 𝔹ush
head (unfold𝔹ush α X fx) = α X fx .proj₁
tail (unfold𝔹ush {𝔽} α X fx)
  = unfold𝔹ush {𝔽} α (Bush X)
  (𝔽 .proj₂ (unfold𝔹ush {𝔽} α X) (α X fx .proj₂))
-}

Func : Set₁
Func = Set → Set

variable 𝔽 𝔾 : Func

_⇒_ : Func → Func → Set₁
F ⇒ G = (X : Set) → F X → G X

H : (Set → Set) → Set → Set
H F X = X × F (F X)

{-
  X   →   ℕ∞      X   →      M S P       
  ↓       ↓       ↓            ↓
1 + X → 1 + ℕ∞  1 + X → ⟦ S ◃ P ⟧ (M S P)

 F  →  Bush     F  →      2M SPPR
 ↓      ↓       ↓            ↓ 
H F → H Bush   H F → 2⟦ SPPR ⟧ (2M SPPR)
-}
    

{-

𝔹ush : Func
𝔹ush = Bush , Bush₁

open import Cont.Cont

{-# TERMINATING #-}

{-
W' : Cont → Set
W' SP = ⟦ SP ⟧ (W' SP)

2W : 2Cont → Cont
2W SPPR = app SPPR (2W SPPR)

R2W : 2Cont → Set → Set
R2W SPPR = ⟦ 2W SPPR ⟧

C2F : Cont → Func
C2F (S ◃ P) = ⟦ S ◃ P ⟧ , ⟦ S ◃ P ⟧₁

{-# TERMINATING #-}
data WW (SPPR : 2Cont) (X : Set) : Set where
  sup : {!!} ⇒ {!!}
-}
-}
