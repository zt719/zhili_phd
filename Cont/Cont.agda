{-# OPTIONS --guardedness #-}

module Cont.Cont where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Function.Base

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

variable
  SP TQ SP' TQ' : Cont

record ContHom (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    f : S → T
    g : (s : S) → Q (f s) → P s

record ⟦_⟧ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    k : P s → X

⟦_⟧₁ : (SP : Cont) {X Y : Set} → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ f sk = sk .s , (f ∘ sk .k)
  where open ⟦_⟧
{-# INLINE ⟦_⟧₁ #-}

⟦_⟧₁' : (SP : Cont) {X Y : Set} → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁' f (s , k) = s , (f ∘ k)

data W (S : Set) (P : S → Set) : Set where
  sup : ⟦ S ◃ P ⟧ (W S P) → W S P

record M (S : Set) (P : S → Set) : Set where
  coinductive
  field
    inf : ⟦ S ◃ P ⟧ (M S P)

⟦_⟧ContHom : {SP TQ : Cont} (fg : ContHom SP TQ)
  → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ f ◃ g ⟧ContHom X (s , k) = f s , (k ∘ g s)

idContHom : ContHom SP SP
idContHom = id ◃ λ s → id

_∘ContHom_ : ContHom TQ TQ' → ContHom SP TQ → ContHom SP TQ'
(f ◃ g) ∘ContHom (h ◃ k) = f ∘ h ◃ λ s → k s ∘ g (h s)

⊤C : Cont
⊤C = ⊤ ◃ const ⊥

⊥C : Cont
⊥C = ⊥ ◃ ⊥-elim

_×C_ : Cont → Cont → Cont
(S ◃ P) ×C (T ◃ Q) = S × T ◃ λ (s , t) → P s ⊎ Q t

{-
  ⟦ S ◃ P ⟧ X × ⟦ T ◃ Q ⟧ X
= (Σ s : S . P s → X) × Σ t : T . Q t → X) -- definition
≃ Σ s : S . Σ t : T . (P s → X) × (Q t → X) -- comm
≃ Σ s : S . Σ t : T . P s ⊎ Q t → X -- distr
≃ Σ (s , t) : S × T . P s ⊎ Q t → X -- assoc
= ⟦ S × T ◃ λ (s , t) → P s ⊎ Q t ⟧ X -- definition
-}

_⊎C_ : Cont → Cont → Cont
(S ◃ P) ⊎C (T ◃ Q) = S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t }

{-
  ⟦ S ◃ P ⟧ X ⊎ ⟦ T ◃ Q ⟧ X
= (Σ s : S . P s → X) ⊎ Σ t : T . Q t → X) -- definition

≃ Σ[ x : S ⊎ T ] case x P Q
= ⟦ S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t } ⟧ X --definition
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
  Σ i : I . ⟦ C i ⟧ X
≃ Σ i : I . ⟦ S i ◃ P i ⟧ X -- rewrite
= Σ i : I . Σ s : S i . (P i s → X) -- definition
≃ Σ (i , s) : Σ I S . (P i s → X) -- unassoc
= ⟦ Σ I S ◃ λ (i , s) → P i s ⟧ X -- definition
-}

ΠC : (I : Set) → (I → Cont) → Cont
ΠC I Cs = ((i : I) → Cs i .S) ◃ λ f → Σ[ i ∈ I ] Cs i .P (f i)
  where open Cont
  
infix 2 ΠC-syntax

ΠC-syntax : (I : Set) → (I → Cont) → Cont
ΠC-syntax = ΠC

syntax ΠC-syntax A (λ x → B) = ΠC[ x ∈ A ] B

{-
  (i : I) → ⟦ C i ⟧ X
= (i : I) → ⟦ S i ◃ P i ⟧ X -- rewrite
= (i : I) → Σ s : S i . (P i s → X) -- definition
≃ Σ f : (i : I) → S i . ((i : I) → P i (f i) → X) -- choice
≃ Σ f : (i : I) → S i . Σ i : I . P i (f i) → X -- curry
= ⟦ (i : I) → S i ◃ λ f → Σ i : I . P i (f i) ⟧ X -- definition
-}

_∘C_ : Cont → Cont → Cont
(S ◃ P) ∘C (T ◃ Q) = (Σ[ s ∈ S ] (P s → T)) ◃ λ (s , f) → Σ[ p ∈ P s ] Q (f p)

{-
  ⟦ S ◃ P ⟧ ∘ ⟦ T ◃ Q ⟧ X
= ⟦ S ◃ P ⟧ (⟦ T ◃ Q ⟧ X)
= Σ s : S . (P s → Σ t : T . (Q t → X))  --definition
≃ Σ s : S . Σ f : P s → T . ((p : P s) → Q (f p) → X)  -- choice
≃ Σ (s , f) : (Σ s : S . P s → T) . ((p : P s) → Q (f p) → X) -- unassoc
≃ Σ (s , f) : (Σ s : S . P s → T) . Σ p : P s . Q (f p) → X -- uncurry
= ⟦ Σ s : S . P s → T ◃ λ (s , f) → Σ p : P s . Q (f p) ⟧ X -- definition
-}

-- Tensor Product
_⊗ContHom_ : ContHom SP TQ → ContHom SP' TQ' → ContHom (SP ∘C SP') (TQ ∘C TQ')
(f ◃ g) ⊗ContHom (f' ◃ g')
  = (λ{ (s , k) → f s , f' ∘ k ∘ g s })
  ◃ λ{ (s , k) (q' , h) → g s q' , g' (k (g s q')) h }

!C : (SP : Cont) → ContHom ⊥C SP
!C (S ◃ P) = (λ ()) ◃ λ ()

¿C : (SP : Cont) → ContHom SP ⊤C
¿C (S ◃ P) = (λ _ → tt) ◃ λ{ s () }

π₁C : ContHom (SP ×C TQ) SP
π₁C = proj₁ ◃ λ{ (S , T) p → inj₁ p }

π₂C : ContHom (SP ×C TQ) TQ
π₂C = proj₂ ◃ λ{ (S , T) q → inj₂ q }

i₁C : ContHom SP (SP ⊎C TQ)
i₁C = inj₁ ◃ λ s p → p

i₂C : ContHom TQ (SP ⊎C TQ)
i₂C = inj₂ ◃ λ s q → q

[_,_]C : ContHom SP TQ → ContHom SP' TQ → ContHom (SP ⊎C SP') TQ
[ f ◃ g , h ◃ k ]C = [ f , h ] ◃ λ{ (inj₁ s) p → g s p ; (inj₂ s') q → k s' q }

<_,_>C : ContHom SP TQ → ContHom SP TQ' → ContHom SP (TQ ×C TQ')
< f ◃ g , h ◃ k >C = < f , h > ◃ λ{ s (inj₁ p) → g s p ; s (inj₂ q) → k s q }
