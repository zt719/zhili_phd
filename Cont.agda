{-# OPTIONS --guardedness --cubical #-}

module Cont where

open import Cubical.Foundations.Prelude
  hiding (_◁_)

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
record _≈_ {A : Type} (xs ys : Stream A) : Type where
  coinductive
  field
    head≡ : head xs ≡ head ys
    tail≈ : tail xs ≈ tail ys
open _≈_

≈→≡ : {A : Type} (xs ys : Stream A) → xs ≈ ys → xs ≡ ys
head (≈→≡ xs ys p i) = head≡ p i
tail (≈→≡ xs ys p i) = ≈→≡ (tail xs) (tail ys) (tail≈ p) i

-- Overview
Fℕ : Type → Type
Fℕ X = ⊤ ⊎ X

FList : Type → Type → Type
FList A X = ⊤ ⊎ A × X

FVec : Type → (ℕ → Type) → (ℕ → Type)
FVec A X n = (n ≡ 0) ⊎ (Σ[ m ∈ ℕ ] (n ≡ suc m) × A × X m)

FTy : Type → Type₁
FTy Γ = Γ → Type

-- Strickly Positive Types
{-# NO_POSITIVITY_CHECK #-}
data Contra : Type where
  c : ((Contra → Bool) → Bool) → Contra

data InfTree : Type where
  leaf : InfTree
  node : (ℕ → InfTree) → InfTree

-- W-Type
data W (S : Type) (P : S → Type) : Type where
  sup-W : (s : S) → (P s → W S P) → W S P

Sℕ : Type
Sℕ = ⊤ ⊎ ⊤

Pℕ : Sℕ → Type
Pℕ (inl tt) = ⊥
Pℕ (inr tt) = ⊤

ℕ′ : Type
ℕ′ = W Sℕ Pℕ

zero′ : ℕ′
zero′ = sup-W (inl tt) (λ ())

suc′ : ℕ′ → ℕ′
suc′ n = sup-W (inr tt) (λ _ → n)

⊤′ : Type
⊤′ = W S P
  where
  S : Type
  S = ⊤
  
  P : S → Type
  P tt = ⊥

tt′ : ⊤′
tt′ = sup-W tt (λ ())

record M (S : Type) (P : S → Type) : Type where
  coinductive
  field
    shape : S
    pos : P shape → M S P
open M

ℕ∞′ : Type
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

-- Container
infix  0 _◁_

record Cont : Type₁ where
  constructor _◁_
  field
    S : Type
    P : S → Type

record Cont-Hom (M N : Cont) : Type where
  constructor _◁_
  open Cont M
  open Cont N renaming (S to T; P to Q)
  field
    u : S → T
    f : (s : S) → Q (u s) → P s

_-C→_ = Cont-Hom

idCont : {SP : Cont} → SP -C→ SP
idCont = id ◁ λ _ → id

∘Cont : {SP TQ WR : Cont} → SP -C→ TQ → TQ -C→ WR → SP -C→ WR
∘Cont (u ◁ f) (v ◁ g)  = v ∘ u ◁ λ s → f s ∘ g (u s)

idlCont : {SP TQ : Cont} (f : SP -C→ TQ)
  → ∘Cont idCont f ≡ f
idlCont f = refl

-- idrCont, assCont

-- Container Extension Functor
record ⟦_⟧ (SP : Cont) (X : Type) : Type where
  constructor _,_
  open Cont SP
  field
    s : S
    p : P s → X

⟦_⟧₁ : (SP : Cont) {X Y : Type}
  → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ S ◁ P ⟧₁ f (s , g) = s , f ∘ g

⟦id⟧ : (SP : Cont) {X : Type}
  → ⟦ SP ⟧₁ {X} id ≡ id
⟦id⟧ (S ◁ P) = refl

⟦∘⟧ : (SP : Cont) {X Y Z : Type} (f : Y → Z) (g : X → Y)
  → ⟦ SP ⟧₁ f ∘ ⟦ SP ⟧₁ g ≡ ⟦ SP ⟧₁ (f ∘ g)
⟦∘⟧ (S ◁ P) f g = refl

⟦_⟧₂ : {SP TQ : Cont} → SP -C→ TQ
   → (X : Type) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ u ◁ f ⟧₂ _ (s , h) = u s , h ∘ f s

⟦nat⟧ : {SP TQ : Cont} (uf : SP -C→ TQ) {X Y : Type} (g : X → Y)
  → ⟦ TQ ⟧₁ g ∘ ⟦ uf ⟧₂ X ≡ ⟦ uf ⟧₂ Y ∘ ⟦ SP ⟧₁ g
⟦nat⟧ (u ◁ f) g = refl

ψ : {SP TQ : Cont}
  → ((X : Type) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X)
  → SP -C→ TQ
ψ {S ◁ P} {T ◁ Q} α = s ∘ m ◁ p ∘ m
  where
  open ⟦_⟧
  m : (s : S) → ⟦ T ◁ Q ⟧ (P s)
  m s = α (P s) (s , id)

sec : {SP TQ : Cont} (uf : SP -C→ TQ)
  → ψ ⟦ uf ⟧₂ ≡ uf
sec (u ◁ f) = refl

ℕ-Cont : Cont
ℕ-Cont = ⊤ ⊎ ⊤ ◁ λ{ (inl tt) → ⊥ ; (inr tt) → ⊤ }

⊤-Cont : Cont
⊤-Cont = ⊤ ◁ λ{ tt → ⊥ }

Tℕ : Type → Type
Tℕ = ⟦ ℕ-Cont ⟧

