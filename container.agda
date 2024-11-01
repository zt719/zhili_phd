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
Pℕ (inl ＊) = ⊥
Pℕ (inr ＊) = ⊤

ℕ' : Set
ℕ' = W Sℕ Pℕ

zero' : ℕ'
zero' = sup-W (inl tt) (λ ())

suc' : ℕ' → ℕ'
suc' n = sup-W (inr tt) (λ _ → n)

⊤' : Set
⊤' = W S P
  where
  S : Set
  S = ⊤
  
  P : S → Set
  P tt = ⊥

tt' : ⊤'
tt' = sup-W tt (λ ())

record M (S : Set) (P : S → Set) : Set where
  coinductive
  field
    shape : S
    pos : P shape → M S P
open M

ℕ∞' : Set
ℕ∞' = M Sℕ Pℕ

zero∞' : ℕ∞'
shape zero∞' = inl tt
pos zero∞' = λ ()

suc∞' : ℕ∞' → ℕ∞'
shape (suc∞' n) = inr tt
pos (suc∞' n) = λ _ → n

∞' : ℕ∞'
shape ∞' = inr tt
pos ∞' = λ _ → ∞'

record M-R {S : Set} {Q : S → Set} (R : M S Q → M S Q → Set) (m₀ m₁ : M S Q) : Set where
  field
    s-eq : shape m₀ ≡ shape m₁
    p-eq : (q₀ : Q (shape m₀)) (q₁ : Q (shape m₁)) (q-eq : PathP (λ i → Q (s-eq i)) q₀ q₁)
      → R (pos m₀ q₀) (pos m₁ q₁)

-- MCoind : {S : Set} {Q : S → Set} 

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
ℕ-Cont = ⊤ ⊎ ⊤ ◃ λ{ (inl tt) → ⊥ ; (inr tt) → ⊤}

⊤-Cont : Cont
⊤-Cont = ⊤ ◃ λ _ → ⊥

-- N-ary Container
record Contₙ {n : ℕ} : Set₁ where
  constructor _◃_
  field
    S : Set
    P : Fin n → S → Set

record _⇒ₙ_ {n : ℕ} (M N : Contₙ {n}) : Set where
  constructor _◃_
  open Contₙ M
  open Contₙ N renaming (S to T; P to Q)
  field
    u : S → T
    f : {i : Fin n} (s : S) → Q i (u s) → P i s

-- Container Extension Functor
record ⟦_⟧ (S◃P : Cont) (X : Set) : Set where
  constructor _,_
  open Cont S◃P
  field
    s : S
    p : P s → X

⟦_⟧₁ : (S◃P : Cont) {X Y : Set} (f : X → Y)
  → ⟦ S◃P ⟧ X → ⟦ S◃P ⟧ Y
⟦ S ◃ P ⟧₁ f (s , g) = (s , f ∘ g)

⟦_⟧₂ : {S◃P T◃Q : Cont} (u◃f : S◃P ⇒ T◃Q)
   → (X : Set) → ⟦ S◃P ⟧ X → ⟦ T◃Q ⟧ X
⟦ u ◃ f ⟧₂ X (s , h) = (u s , h ∘ f s)

record ⟦_⟧ₙ {n : ℕ} (S◃P : Contₙ {n}) (X : Fin n → Set) : Set where
  constructor _,_
  open Contₙ S◃P
  field
    s : S
    p : {i : _} → P i s → X i

⟦_⟧ₙ₁ : {n : ℕ} (S◃P : Contₙ {n})
  → {X Y : Fin n → Set} (f : {i : _} → X i → Y i) 
  → ⟦ S◃P ⟧ₙ X → ⟦ S◃P ⟧ₙ Y
⟦ S ◃ P ⟧ₙ₁ f (s , g) = (s , f ∘ g)

⟦_⟧ₙ₂ : {n : ℕ} {S◃P T◃Q : Contₙ {n}} (u◃f : S◃P ⇒ₙ T◃Q)
  → (X : Fin n → Set) → ⟦ S◃P ⟧ₙ X → ⟦ T◃Q ⟧ₙ X
⟦ u ◃ f ⟧ₙ₂ X (s , h) = (u s , h ∘ f s)

fst : {S◃P : Cont} {X : Set} → ⟦ S◃P ⟧ X → Cont.S S◃P
fst = ⟦_⟧.s

snd : {S◃P : Cont} {X : Set} (r : ⟦ S◃P ⟧ X) → Cont.P S◃P (⟦_⟧.s r) → X
snd = ⟦_⟧.p

from : {S◃P T◃Q : Cont} (α : (X : Set) → ⟦ S◃P ⟧ X → ⟦ T◃Q ⟧ X) → S◃P ⇒ T◃Q
from {S ◃ P} {T ◃ Q} α = (fst ∘ m) ◃ (snd ∘ m)
  where
  m : (s : S) → ⟦ T ◃ Q ⟧ (P s)
  m s = α (P s) (s , id)

-- bijection : {S◃P T◃Q : Cont} (α : (X : Set) → ⟦ S◃P ⟧ X → ⟦ T◃Q ⟧ X) (X : Set) (sf : ⟦ S◃P ⟧ X)
--  → ⟦ from α ⟧₂ X sf ≡ α X sf
-- bijection {S ◃ P} {T ◃ Q} α X (s , f) = {!!}
