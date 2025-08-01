module Cont.Cont where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Function.Base

{- Container -}
infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

private variable SP TQ SP' TQ' : Cont

{- Container Hom -}
record ContHom (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    f : S → T
    g : (s : S) → Q (f s) → P s

{- Container Extension Functor -}
record ⟦_⟧₀ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    k : P s → X

⟦_⟧₁ : (SP : Cont) {X Y : Set} → (X → Y) → ⟦ SP ⟧₀ X → ⟦ SP ⟧₀ Y
⟦ SP ⟧₁ f sk = sk .s , (f ∘ sk .k)
  where open ⟦_⟧₀
{-# INLINE ⟦_⟧₁ #-}

⟦_⟧₁' : (SP : Cont) {X Y : Set} → (X → Y) → ⟦ SP ⟧₀ X → ⟦ SP ⟧₀ Y
⟦ SP ⟧₁' f (s , k) = s , (f ∘ k)

⟦_⟧Hom : {SP TQ : Cont} (fg : ContHom SP TQ)
  → (X : Set) → ⟦ SP ⟧₀ X → ⟦ TQ ⟧₀ X
⟦ f ◃ g ⟧Hom X (s , k) = f s , (k ∘ g s)

zeroC : Cont
zeroC = ⊥ ◃ λ ()

oneC : Cont
oneC = ⊤ ◃ λ{ tt → ⊥ }

_×C_ : Cont → Cont → Cont
(S ◃ P) ×C (T ◃ Q) = S × T ◃ λ (s , t) → P s ⊎ Q t

{-
  ⟦ S ◃ P ⟧₀ X × ⟦ T ◃ Q ⟧₀ X
= (Σ s : S . P s → X) × Σ t : T . Q t → X) -- definition
≃ Σ s : S . Σ t : T . (P s → X) × (Q t → X) -- comm
≃ Σ s : S . Σ t : T . P s ⊎ Q t → X -- distr
≃ Σ (s , t) : S × T . P s ⊎ Q t → X -- assoc
= ⟦ S × T ◃ λ (s , t) → P s ⊎ Q t ⟧₀ X -- definition
-}

_⊎C_ : Cont → Cont → Cont
(S ◃ P) ⊎C (T ◃ Q) = S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t }

{-
  ⟦ S ◃ P ⟧₀ X ⊎ ⟦ T ◃ Q ⟧₀ X
= (Σ s : S . P s → X) ⊎ Σ t : T . Q t → X) -- definition

≃ Σ[ x : S ⊎ T ] case x P Q
= ⟦ S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t } ⟧₀ X --definition


-}

_∘C_ : Cont → Cont → Cont
(S ◃ P) ∘C (T ◃ Q) = (Σ[ s ∈ S ] (P s → T)) ◃ λ (s , f) → Σ[ p ∈ P s ] Q (f p)

{-
  ⟦ S ◃ P ⟧₀ ∘ ⟦ T ◃ Q ⟧₀ X
= ⟦ S ◃ P ⟧₀ (⟦ T ◃ Q ⟧₀ X)
= Σ s : S . (P s → Σ t : T . (Q t → X))  --definition
≃ Σ s : S . Σ f : P s → T . ((p : P s) → Q (f p) → X)  -- choice
≃ Σ (s , f) : (Σ s : S . P s → T) . ((p : P s) → Q (f p) → X) -- unassoc
≃ Σ (s , f) : (Σ s : S . P s → T) . Σ p : P s . Q (f p) → X -- uncurry
= ⟦ Σ s : S . P s → T ◃ λ (s , f) → Σ p : P s . Q (f p) ⟧₀ X -- definition
-}

ΣC : (I : Set) → (I → Cont) → Cont
ΣC I Cs = Σ[ i ∈ I ] Cs i .S ◃ λ (i , s) → Cs i .P s
  where open Cont

infix 2 ΣC-syntax

ΣC-syntax : (I : Set) → (I → Cont) → Cont
ΣC-syntax = ΣC

syntax ΣC-syntax A (λ x → B) = ΣC[ x ∈ A ] B

-- ΣC-syntax

{-
  Σ i : I . ⟦ C i ⟧₀ X
≃ Σ i : I . ⟦ S i ◃ P i ⟧₀ X -- rewrite
= Σ i : I . Σ s : S i . (P i s → X) -- definition
≃ Σ (i , s) : Σ I S . (P i s → X) -- unassoc
= ⟦ Σ I S ◃ λ (i , s) → P i s ⟧₀ X -- definition
-}

ΠC : (I : Set) → (I → Cont) → Cont
ΠC I Cs = ((i : I) → Cs i .S) ◃ λ f → Σ[ i ∈ I ] Cs i .P (f i)
  where open Cont
  
infix 2 ΠC-syntax

ΠC-syntax : (I : Set) → (I → Cont) → Cont
ΠC-syntax = ΠC

syntax ΠC-syntax A (λ x → B) = ΠC[ x ∈ A ] B


{-
  (i : I) → ⟦ C i ⟧₀ X
= (i : I) → ⟦ S i ◃ P i ⟧₀ X -- rewrite
= (i : I) → Σ s : S i . (P i s → X) -- definition
≃ Σ f : (i : I) → S i . ((i : I) → P i (f i) → X) -- choice
≃ Σ f : (i : I) → S i . Σ i : I . P i (f i) → X -- curry
= ⟦ (i : I) → S i ◃ λ f → Σ i : I . P i (f i) ⟧₀ X -- definition
-}



! : (SP : Cont) → ContHom zeroC SP
! (S ◃ P) = f ◃ λ ()
  where
  f : ⊥ → S
  f = λ ()

¿ : (SP : Cont) → ContHom SP oneC
¿ (S ◃ P) = f ◃ g
  where
  f : S → ⊤
  f s = tt

  g : (s : S) → ⊥ → P s
  g s = λ ()

[_,_]C : ContHom SP TQ → ContHom SP' TQ → ContHom (SP ⊎C SP') TQ
[ f ◃ g , h ◃ k ]C = [ f , h ] ◃ λ{ (inj₁ s) q → g s q ; (inj₂ s') q → k s' q }

variable
  X Y Z : Set

record Func : Set₁ where
  constructor _,_
  field
    F₀ : Set → Set
    F₁ : (X → Y) → F₀ X → F₀ Y

NatTrans : Func → Func → Set₁
NatTrans (F₀ , F₁) (G₀ , G₁) = (X : Set) → F₀ X → G₀ X

⟦_⟧ : Cont → Func
⟦ SP ⟧ = ⟦ SP ⟧₀ , ⟦ SP ⟧₁

