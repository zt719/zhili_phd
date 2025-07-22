{-# OPTIONS --guardedness --cubical #-}

open import Cubical.Foundations.Prelude

record M (S : Type) (P : S → Type) : Type where
  coinductive
  field
    shape : S
    pos : P shape → M S P
open M    

record M-R {S P} (R : M S P → M S P → Type) (m n : M S P) : Type where
  coinductive
  field
    s-eq : m .shape ≡ n .shape
    p-eq : (p : P (m .shape)) (q : P (n .shape))
      → PathP (λ i → P (s-eq i)) p q
      → R (pos m p) (pos n q)

{- I-ary Container -}

record ICont {I : Type} : Type₁ where
  constructor _,_
  field
    S : Type
    P : I → S → Type

record IContHom {I} (SP TQ : ICont {I}) : Type where
  constructor _,_
  open ICont SP
  open ICont TQ renaming (S to T ; P to Q)
  field
    f : S → T
    g : (i : I) (s : S) → Q i (f s) → P i s

record ⟦_⟧₀ {I : Type} (SP : ICont {I}) (X : I → Type) : Type where
  constructor _,_
  open ICont SP
  field
    s : S
    k : (i : I) → P i s → X i

⟦_⟧₁ : {I : Type} (SP : ICont {I}) {X Y : I → Type}
  → ((i : I) → X i → Y i)
  → ⟦ SP ⟧₀ X → ⟦ SP ⟧₀ Y
⟦ SP ⟧₁ f (s , k) = s , λ i z → f i (k i z)

⟦_⟧Hom : {I : Type} {SP TQ : ICont {I}} → IContHom SP TQ
  → {X : I → Type} (i : I) → ⟦ SP ⟧₀ X → ⟦ TQ ⟧₀ X
⟦ f , g ⟧Hom i (s , k) = f s , λ j p → k j (g j s p)

{- (I+1)-ary Container -}

record I+Cont {I : Type} : Type₁ where
  constructor _◃_,_
  field
    S : Type
    P : I → S → Type
    Q : S → Type

record ⟦_⟧+₀ {I} (SPQ : I+Cont {I}) (X : I → Type) (Y : Type) : Type where
  constructor _,_,_
  open I+Cont SPQ
  field
    s : S
    k : (i : I) → P i s → X i
    t : Q s → Y

open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

F : Set → Set → Set
F A X = ⊤ ⊎ A × X

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

FI+Cont : I+Cont {⊤}
FI+Cont = S ◃ P₀ , P₁
  where
  S : Type
  S = ⊤ ⊎ ⊤

  P₀ : ⊤ → S → Type
  P₀ tt (inl tt) = ⊥
  P₀ tt (inr tt) = ⊤

  P₁ : S → Type
  P₁ (inl tt) = ⊥
  P₁ (inr tt) = ⊤

record FixedPoint (S : Type) (P : S → Type) : Type₁ where
  field
    C : Type
    χ : Σ[ s ∈ S ] (P s → C) ≡ C

open import Cubical.Data.Nat
open import Cubical.Data.Fin

{-
⟦ S ◃ P , Q ⟧ X (⟦ C ◃ B ⟧ X)
= Σ s : S . (((i : I) → P i s → X i) × (Q s → ⟦ C ◃ B ⟧ X))
= Σ s : S . (((i : I) → P i s → X i) × (Q s → Σ c : C . ((i : I) → B i c → X i)))
≅ Σ s : S . (((i : I) → P i s → X i) × (Σ f : Q s → C . ((q : Q s) (i : I) → B i (f q) → X i)))
≅ Σ s : S . Σ f : Q s → C . (((i : I) → P i s → X i) × ((q : Q s) (i : I) → B i (f q) → X i))
≅ Σ s : S . Σ f : Q s → C . (((i : I) → P i s → X i) × ((i : I) (q : Q s) → B i (f q) → X i))
≅ Σ s : S . Σ f : Q s → C . ((i : I) → (P i s → X i) × ((q : Q s) → B i (f q) → X i))
≅ Σ s : S . Σ f : Q s → C . ((i : I) → (P i s → X i) × (Σ q : Q s . B i (f q) → X i))
≅ Σ s : S . Σ f : Q s → C . ((i : I) → P i s + Σ q : Q s . B i (f q) → X i)
≅ Σ (s , f) : (Σ s : S . Q s → C) . ((i : I) → P i s + Σ q : Q s . B i (f q) → X i)
= ⟦ (Σ s : S . Q s → C) ◃ λ i (s , f) → P i s + Σ q : Q s . B i (f q) ⟧ X
-}

-- data Pos (φ : FixedPoint S P)
