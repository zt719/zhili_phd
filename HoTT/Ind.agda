{-# OPTIONS --guardedness #-}

open import Data.Unit
open import Data.Product
open import Data.Sum

{- Inductive Type -}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{- Iteration -}

itℕ : (A : Set)
  → A
  → (A → A)
  → ℕ → A
itℕ A z s zero = z
itℕ A z s (suc n) = s (itℕ A z s n)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_+it_ : ℕ → ℕ → ℕ
_+it_ = itℕ (ℕ → ℕ) (λ n → n) (λ m+ n → suc (m+ n))

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

_*it_ : ℕ → ℕ → ℕ
_*it_ = itℕ (ℕ → ℕ) (λ n → zero) (λ m* n → n + m* n)

{- Recursion -}

recℕ : (A : Set)
  → A
  → (ℕ → A → A)
  → ℕ → A
recℕ A z s zero = z
recℕ A z s (suc n) = s n (recℕ A z s n)

_! : ℕ → ℕ
zero ! = suc zero
suc n ! = suc n * n

_!rec : ℕ → ℕ
_!rec = recℕ ℕ (suc zero) (λ n n! → suc n * n!)

{- Induction -}

indℕ : (P : ℕ → Set)
  → P zero
  → ((n : ℕ) → P n → P (suc n))
  → (n : ℕ) → P n
indℕ P z s zero = z
indℕ P z s (suc n) = s n (indℕ P z s n)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

refl≤ : (n : ℕ) → n ≤ n
refl≤ zero = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

refl≤-ind : (n : ℕ) → n ≤ n
refl≤-ind = indℕ (λ n → n ≤ n) z≤n (λ n n≤n → s≤s n≤n)

{- Iteration ↔ Recusion -}

itℕ-recℕ : (A : Set)
  → A
  → (A → A)
  → ℕ → A
itℕ-recℕ A z s n = recℕ A z (λ _ → s) n

recℕ-itℕ : (A : Set)
  → A
  → (ℕ → A → A)
  → ℕ → A
recℕ-itℕ A z s n = proj₂ (itℕ (ℕ × A) z' s' n)
  where
  z' : ℕ × A
  z' = zero , z

  s' : ℕ × A → ℕ × A
  s' (n , a) = suc n , s n a

{- Recursion is non-dependent induction -}

recℕ-indℕ : (A : Set)
  → A
  → (ℕ → A → A)
  → ℕ → A
recℕ-indℕ A = indℕ (λ _ → A)

-------------------------------------------

{- Coinductive Type -}

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : ⊤ ⊎ ℕ∞
open ℕ∞

{- Coiteration -}

coitℕ∞ : (A : Set)
  → (A → ⊤ ⊎ A)
  → A → ℕ∞
pred∞ (coitℕ∞ A p a) with p a
... | inj₁ tt = inj₁ tt
... | inj₂ a' = inj₂ (coitℕ∞ A p a')

zero∞ : ℕ∞
pred∞ zero∞ = inj₁ tt

zero∞-coit : ℕ∞
zero∞-coit = coitℕ∞ ⊤ inj₁ tt

suc∞ : ℕ∞ → ℕ∞
pred∞ (suc∞ n) = inj₂ n

suc∞-coit : ℕ∞ → ℕ∞
suc∞-coit = coitℕ∞ ℕ∞ inj₂

∞ : ℕ∞
pred∞ ∞ = inj₂ ∞

∞-coit : ℕ∞
∞-coit = coitℕ∞ ⊤ inj₂ tt

{- Corecursion -}

corecℕ∞ : (A : Set)
  → (A → ℕ∞ ⊎ (⊤ ⊎ A))
  → A → ℕ∞
pred∞ (corecℕ∞ A p a) with p a
... | inj₁ n = pred∞ n
... | inj₂ (inj₁ tt) = inj₁ tt
... | inj₂ (inj₂ a') = inj₂ (corecℕ∞ A p a')

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m +∞ n) with pred∞ m
... | inj₁ tt = pred∞ n
... | inj₂ m' = inj₂ (m' +∞ n)

_*∞_+∞_ : ℕ∞ → ℕ∞ → ℕ∞ → ℕ∞
pred∞ (m *∞ n +∞ k) with pred∞ m
... | inj₁ tt = inj₂ k
... | inj₂ m' = inj₂ (m' *∞ n +∞ (n +∞ k))

_*∞_ : ℕ∞ → ℕ∞ → ℕ∞
m *∞ n = m *∞ n +∞ zero∞

{- Coiteration ↔ Corecursion -}

coitℕ∞-corecℕ∞ : (A : Set)
  → (A → ⊤ ⊎ A)
  → A → ℕ∞
coitℕ∞-corecℕ∞ A p a = corecℕ∞ A (λ a → inj₂ (p a)) a

corecℕ∞-coitℕ∞ : (A : Set)
  → (A → ℕ∞ ⊎ (⊤ ⊎ A))
  → A → ℕ∞
corecℕ∞-coitℕ∞ A p a = coitℕ∞ (ℕ∞ ⊎ A) p' a'
  where
  p' : ℕ∞ ⊎ A → ⊤ ⊎ (ℕ∞ ⊎ A)
  p' = inj₂
  
  a' : ℕ∞ ⊎ A
  a' = inj₂ a
