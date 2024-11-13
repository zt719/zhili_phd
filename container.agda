{-# OPTIONS --guardedness --cubical #-}

module Container where

open import Cubical.Foundations.Prelude using (PathP; _≡_; refl)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_)
open import Cubical.Data.Vec using (Vec)
open import Cubical.Codata.Stream using (Stream)
open Stream
open import Cubical.Data.Fin using (Fin; fzero; fsuc)

open import Function using (id; _∘_)

-- Cubical
record _≈_ {A : Set} (xs ys : Stream A) : Set where
  coinductive
  field
    head≡ : head xs ≡ head ys
    tail≈ : tail xs ≈ tail ys
open _≈_

≈→≡ : {A : Set} (xs ys : Stream A) → xs ≈ ys → xs ≡ ys
head (≈→≡ xs ys p i) = head≡ p i
tail (≈→≡ xs ys p i) = ≈→≡ (tail xs) (tail ys) (tail≈ p) i

-- Overview
Fℕ : Set → Set
Fℕ X = ⊤ ⊎ X

FList : Set → Set → Set
FList A X = ⊤ ⊎ A × X

FVec : Set → (ℕ → Set) → (ℕ → Set)
FVec A X n = (n ≡ 0) ⊎ (Σ[ m ∈ ℕ ] (n ≡ suc m) × A × X m)

FTy : Set → Set₁
FTy Γ = Γ → Set

-- Strickly Positive Sets
{-# NO_POSITIVITY_CHECK #-}
data Contra : Set where
  c : ((Contra → Bool) → Bool) → Contra

data InfTree : Set where
  leaf : InfTree
  node : (ℕ → InfTree) → InfTree

-- W-Set
data W (S : Set) (P : S → Set) : Set where
  sup-W : (s : S) → (P s → W S P) → W S P

Sℕ : Set
Sℕ = ⊤ ⊎ ⊤

Pℕ : Sℕ → Set
Pℕ (inl tt) = ⊥
Pℕ (inr tt) = ⊤

ℕ′ : Set
ℕ′ = W Sℕ Pℕ

zero′ : ℕ′
zero′ = sup-W (inl tt) (λ ())

suc′ : ℕ′ → ℕ′
suc′ n = sup-W (inr tt) (λ _ → n)

⊤′ : Set
⊤′ = W S P
  where
  S : Set
  S = ⊤
  
  P : S → Set
  P tt = ⊥

tt′ : ⊤′
tt′ = sup-W tt (λ ())

record M (S : Set) (P : S → Set) : Set where
  coinductive
  field
    shape : S
    pos : P shape → M S P
open M

ℕ∞′ : Set
ℕ∞′ = M Sℕ Pℕ

zero∞′ : ℕ∞′
shape zero∞′ = inl tt
pos zero∞′ = λ ()

suc∞′ : ℕ∞′ → ℕ∞′
shape (suc∞′ n) = inr tt
pos (suc∞′ n) = λ _ → n

∞′ : ℕ∞′
shape ∞′ = inr tt
pos ∞′ = λ _ → ∞′

record M-R {S : Set} {Q : S → Set} (R : M S Q → M S Q → Set) (m₀ m₁ : M S Q) : Set where
  field
    s-eq : shape m₀ ≡ shape m₁
    p-eq : (q₀ : Q (shape m₀)) (q₁ : Q (shape m₁)) (q-eq : PathP (λ i → Q (s-eq i)) q₀ q₁)
      → R (pos m₀ q₀) (pos m₁ q₁)

-- Container
infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

record _⇒_ (M N : Cont) : Set where
  constructor _◃_
  open Cont M
  open Cont N renaming (S to T; P to Q)
  field
    u : S → T
    f : (s : S) → Q (u s) → P s

ℕ-Cont : Cont
ℕ-Cont = ⊤ ⊎ ⊤ ◃ λ{ (inl tt) → ⊥ ; (inr tt) → ⊤ }

⊤-Cont : Cont
⊤-Cont = ⊤ ◃ λ{ tt → ⊥ }

-- Container Extension Functor
record ⟦_⟧ (S◃P : Cont) (X : Set) : Set where
  constructor _,_
  open Cont S◃P
  field
    s : S
    p : P s → X

⟦_⟧₁ : (S◃P : Cont) {X Y : Set} (f : X → Y)
  → ⟦ S◃P ⟧ X → ⟦ S◃P ⟧ Y
⟦ S ◃ P ⟧₁ f (s , g) = s , f ∘ g

⟦id⟧₁ : (S◃P : Cont) {X : Set}
  → ⟦ S◃P ⟧₁ {X} id ≡ id
⟦id⟧₁ (S ◃ P) = refl

⟦∘⟧₁ : (S◃P : Cont) {X Y Z : Set} (f : Y → Z) (g : X → Y)
  → ⟦ S◃P ⟧₁ f ∘ ⟦ S◃P ⟧₁ g ≡ ⟦ S◃P ⟧₁ (f ∘ g)
⟦∘⟧₁ (S ◃ P) f g = refl

⟦_⟧₂ : {S◃P T◃Q : Cont} (u◃f : S◃P ⇒ T◃Q)
   → (X : Set) → ⟦ S◃P ⟧ X → ⟦ T◃Q ⟧ X
⟦ u ◃ f ⟧₂ X (s , h) = u s , h ∘ f s

natural : {S◃P T◃Q : Cont} (u◃f : S◃P ⇒ T◃Q) {X Y : Set} (g : X → Y)
  → ⟦ T◃Q ⟧₁ g ∘ ⟦ u◃f ⟧₂ X ≡ ⟦ u◃f ⟧₂ Y ∘ ⟦ S◃P ⟧₁ g
natural (u ◃ f) g = refl

from : {S◃P T◃Q : Cont} (α : (X : Set) → ⟦ S◃P ⟧ X → ⟦ T◃Q ⟧ X)
  → S◃P ⇒ T◃Q
from {S ◃ P} {T ◃ Q} α = ⟦_⟧.s ∘ m ◃ ⟦_⟧.p ∘ m
  where
  m : (s : S) → ⟦ T ◃ Q ⟧ (P s)
  m s = α (P s) (s , id)

from∘to : {S◃P T◃Q : Cont} (u◃f : S◃P ⇒ T◃Q)
  → from (⟦ u◃f ⟧₂) ≡ u◃f
from∘to (u ◃ f) = refl

Tℕ : Set → Set
Tℕ X = ⊤ ⊎ X

Tℕ′ : Set → Set
Tℕ′ = ⟦ ℕ-Cont ⟧
