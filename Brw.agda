{-
{-# OPTIONS --cubical --guardedness #-}

module Brw where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

module Simulations {ℓ₁ ℓ₂} (A : Type ℓ₁) (_≼_ : A → A → Type ℓ₂) where

  _≲_ : (f g : ℕ → A) → Type _
  f ≲ g = ∀ k → Σ[ n ∈ ℕ ] f k ≼ g n

  _≈_ : (f g : ℕ → A) → Type _
  f ≈ g = Σ (f ≲ g) (λ _ → g ≲ f)

mutual
  data Brw : Type
  data _≤_ : Brw → Brw → Type

  open Simulations Brw _≤_ public

  data Brw where
    zero  : Brw
    succ  : Brw → Brw
    limit : (f : ℕ → Brw) → {f↑ : increasing f} → Brw
    bisim : ∀ f {f↑} g {g↑} →
            f ≈ g →
            limit f {f↑} ≡ limit g {g↑}
--    trunc : (x y : Brw) → (p q : x ≡ y) → p ≡ q

  data _≤_ where
    ≤-zero      : ∀ {x} → zero ≤ x
--    ≤-trans     : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-suc : ∀ {x y} → x ≤ y → succ x ≤ succ y
    ≤-cocone    : ∀ {x} f {f↑ k} → (x ≤ f k) → (x ≤ limit f {f↑})
    ≤-limiting  : ∀ f {f↑ x} → ((k : ℕ) → f k ≤ x) → limit f {f↑} ≤ x
--    ≤-trunc     : ∀ {x y} → (p q : x ≤ y) → p ≡ q

  _<_ : Brw → Brw → Type
  x < y = succ x ≤ y

  increasing : (ℕ → Brw) → Type
  increasing f = ∀ k → f k < f (suc k)

  ≤-trans     : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans {x} {y} {z} ≤-zero q = ≤-zero
  ≤-trans {x} {y} {zero} (≤-suc p) q = _
  ≤-trans {x} {y} {succ z} (≤-suc p) q = ≤-suc {!!}
  ≤-trans {x} {y} {limit f} (≤-suc p) q = {!!}
  ≤-trans {x} {y} {bisim f g x₁ i} (≤-suc p) q = {!!}
  ≤-trans {x} {y} {z} (≤-cocone f p) q = {!!}
  ≤-trans {x} {y} {z} (≤-limiting f x₁) q = {!!}

{-
  ≤-trans : ∀ {m n k} → m ≤ n → n ≤ k → m ≤ k
  ≤-trans ≤-zero x₁ = ≤-zero
  ≤-trans (≤-suc x) (≤-suc x₁) = ≤-suc (≤-trans x x₁)
  ≤-trans (≤-suc x) (≤-cocone i x₁) = ≤-cocone i (≤-trans (≤-suc x) x₁)
  ≤-trans (≤-cocone i x) (≤-cocone i₁ x₁) = ≤-cocone i₁ (≤-trans (≤-cocone i x) x₁)
  ≤-trans (≤-cocone i x) (≤-limiting x₁) = ≤-trans x (x₁ i)
  ≤-trans (≤-limiting x) x₁ = ≤-limiting (λ i → ≤-trans (x i) x₁)
-}
-}

module Brw where

-- {-# OPTIONS --guardedness #-}

open import Data.Nat hiding (_≤_; _<_)
open import Data.Product

open import Relation.Binary.PropositionalEquality

module Simulations {ℓ₁ ℓ₂} {A : Set ℓ₁} {_≼_ : A → A → Set ℓ₂} where

  _≲_ : (f g : ℕ → A) → Set _
  f ≲ g = ∀ k → Σ[ n ∈ ℕ ] f k ≼ g n

  _≈_ : (f g : ℕ → A) → Set _
  f ≈ g = Σ (f ≲ g) (λ _ → g ≲ f)

open Simulations

data Brw : Set

data _≤_ : Brw → Brw → Set

increasing : (ℕ → Brw) → Set

data Brw where
  zero  : Brw
  suc  : Brw → Brw
  limit : (f : ℕ → Brw) → {f↑ : increasing f} → Brw
--  trunc : (x y : Brw) → (p q : x ≡ y) → p ≡ q


postulate
  bisim : ∀ (f : ℕ → Brw) {f↑ : increasing f} (g : ℕ → Brw) {g↑ : increasing g} →
    _≈_ {A = Brw} {_≼_ = _≤_} f g → limit f {f↑} ≡ limit g {g↑}


data _≤_ where
  ≤-zero      : ∀ {x} → zero ≤ x
--  ≤-trans     : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-suc : ∀ {x y} → x ≤ y → suc x ≤ suc y
  ≤-cocone    : ∀ {x} f {f↑ k} → (x ≤ f k) → (x ≤ limit f {f↑})
  ≤-limiting  : ∀ f {f↑ x} → ((k : ℕ) → f k ≤ x) → limit f {f↑} ≤ x
  --≤-trunc     : ∀ {x y} → (p q : x ≤ y) → p ≡ q

_<_ : Brw → Brw → Set
x < y = suc x ≤ y

increasing f = ∀ k → f k < f (suc k)

≤-refl : ∀ {m} → m ≤ m
≤-refl {zero} = ≤-zero
≤-refl {suc m} = ≤-suc ≤-refl
≤-refl {limit f} = ≤-limiting f (λ k → ≤-cocone f ≤-refl)

≤-trans : ∀ {m n k} → m ≤ n → n ≤ k → m ≤ k
≤-trans ≤-zero x₁ = ≤-zero
≤-trans (≤-suc x) (≤-suc x₁) = ≤-suc (≤-trans x x₁)
≤-trans (≤-suc x) (≤-cocone f x₁) = ≤-cocone f (≤-trans (≤-suc x) x₁)
≤-trans (≤-cocone f x) (≤-cocone f₁ x₁) = ≤-cocone f₁ (≤-trans (≤-cocone f x) x₁)
≤-trans (≤-cocone f x) (≤-limiting .f x₁) = ≤-trans x (x₁ _)
≤-trans (≤-limiting f x) x₁ = ≤-limiting f (λ k → ≤-trans (x k) x₁)
