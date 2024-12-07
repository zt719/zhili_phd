{-# OPTIONS --guardedness --cubical #-}

module Bush where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
  
record Bush (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Bush (Bush A)
open Bush

{-# TERMINATING #-}
Bush₁ : {X Y : Set} → (X → Y) → Bush X → Bush Y
head (Bush₁ f bx) = f (head bx)
tail (Bush₁ f bx) = Bush₁ (Bush₁ f) (tail bx)

private module _ where

  data BT : Set where
    leaf : BT
    node : BT → BT → BT

  {-# TERMINATING #-}
  φ₁ : {A : Set} → (BT → A) → Bush A
  head (φ₁ f) = f leaf
  tail (φ₁ f) = φ₁ (λ l → φ₁ (λ r → f (node l r)))

  ψ₁ : {A : Set} → Bush A → BT → A
  ψ₁ bsh leaf = head bsh
  ψ₁ bsh (node l r) = ψ₁ (ψ₁ (tail bsh) l) r

  {-# TERMINATING #-}
  retr₁ : {A : Set} (f : BT → A) → ψ₁ (φ₁ f) ≡ f
  retr₁ f i leaf = f leaf
  retr₁ f i (node l r) = (
    ψ₁ (φ₁ f) (node l r)
      ≡⟨ (λ j → ψ₁ (retr₁ (λ l′ → φ₁ (λ r′ → f (node l′ r′))) j l) r) ⟩
    ψ₁ (φ₁ (λ r′ → f (node l r′))) r
      ≡⟨ (λ j → retr₁ (λ r′ → f (node l r′)) j r) ⟩ 
    f (node l r) ∎ 
    ) i

  {-# TERMINATING #-}
  sec₁ : {A : Set} (as : Bush A) → φ₁ (ψ₁ as) ≡ as
  head (sec₁ as i) = head as
  tail (sec₁ as i) = (
    tail (φ₁ (ψ₁ as))
      ≡⟨ (λ j → φ₁ (λ l′ → sec₁ (ψ₁ (tail as) l′) j)) ⟩
    φ₁ (ψ₁ (tail as))
      ≡⟨ sec₁ (tail as) ⟩
    tail as ∎
    ) i

  thePath₁ : {A : Set} → (BT → A) ≡ Bush A
  thePath₁ = isoToPath (iso φ₁ ψ₁ sec₁ retr₁)
