{-# OPTIONS --guardedness #-}

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

variable
  X Y : Set

{- W and M types -}

data W (S : Set) (P : S → Set) : Set where
  sup : Σ[ s ∈ S) → (P s → W S P) → W S P

foldW : {S : Set} {P : S → Set} (f : (s : S) → (P s → X) → X)
  → W S P → X
foldW f (sup s k) = f s (foldW f ∘ k)

record M (S : Set) (P : S → Set) : Set where
  coinductive
  field
    inf : (s : S) → P s → M S P
open M    


unfold : {S : Set} {P : S → Set} (f : X → Σ[ s ∈ S ] (P s → X))
  → X → M S P
inf (unfold f x) with f x
... | s , f = {!!}
-- ... | s , k = s , unfold f ∘ k

{-
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
-}
