{-# OPTIONS --guardedness #-}

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

variable
  X Y : Set

{- Containers -}

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

record ⟦_⟧ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    k : P s → X

⟦_⟧₁ : (SP : Cont)
  → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ f (s , k) = s , f ∘ k

{- W and M types -}

data W (S : Set) (P : S → Set) : Set where
  sup : ⟦ S ◃ P ⟧ (W S P) → W S P

fold : {S : Set} {P : S → Set} (f : ⟦ S ◃ P ⟧ X → X)
  → W S P → X
fold f (sup (s , k)) = f (s , fold f ∘ k)

record M (S : Set) (P : S → Set) : Set where
  coinductive
  field
    inf : ⟦ S ◃ P ⟧ (M S P)
open M    

unfold : {S : Set} {P : S → Set} (f : X → ⟦ S ◃ P ⟧ X)
  → X → M S P
inf (unfold f x) with f x
... | s , k = s , unfold f ∘ k

{- ℕ and ℕ∞ -}

S : Set
S = ⊤ ⊎ ⊤

P : S → Set
P (inj₁ tt) = ⊥
P (inj₂ tt) = ⊤

ℕ : Set
ℕ = W S P

zero : ℕ
zero = sup (inj₁ tt , λ ())

suc : ℕ → ℕ
suc (sup x) = sup (inj₂ tt , λ p → sup x)

ℕ∞ : Set
ℕ∞ = M S P

zero∞ : ℕ∞
inf zero∞ = inj₁ tt , λ ()

suc∞ : ℕ∞ → ℕ∞
inf (suc∞ n) = inj₂ tt , λ p → n

∞ : ℕ∞
inf ∞ = inj₂ tt , λ p → ∞
