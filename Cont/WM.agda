{-# OPTIONS --guardedness #-}

module Cont.WM where

open import Cont.Cont
open import Data.Product
open import Data.Sum
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_])

postulate
  funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
    {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

Σ≡ :
  ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
  Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂) →
  (a₁ , b₁) ≡ (a₂ , b₂)
Σ≡ (refl , refl) = refl

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

W₁ : SP →ᶜ TQ → W SP → W TQ
W₁ (g ◃ h) (sup (s , f)) = sup (g s , λ q → W₁ (g ◃ h) (f (h s q)))

module _ (X : Set) (SP : Cont) (α : ⟦ SP ⟧ X → X) where

  itW : W SP → X
  itW (sup (s , f)) = α (s , itW ∘ f)

  commute : itW ∘ sup ≡ α ∘ ⟦ SP ⟧₁ itW
  commute = funExt (λ _ → refl)

  !itW : (itW' : W SP → X)
    (commuteW' : (sf : ⟦ SP ⟧ (W SP)) → itW' (sup sf) ≡ α (⟦ SP ⟧₁ itW' sf))
    → (w : W SP) → itW' w ≡ itW w
  !itW itW' commuteW' (sup (s , f)) = trans (commuteW' (s , f))
    (cong α (Σ≡ (refl , funExt λ a → !itW itW' commuteW' (f a))))

module _ (X : Set) (SP : Cont) (α : ⟦ SP ⟧ (W SP × X) → X) where

  recW : W SP → X
  recW (sup (s , f)) = α (s , < f , recW ∘ f >)
    
elimW : {S : Set} {P : S → Set}
  → (Q : W (S ◃ P) → Set)
  → (((s , f) : ⟦ S ◃ P ⟧ (W (S ◃ P))) → ((p : P s) → Q (f p)) → Q (sup (s , f)))
  → (w : W (S ◃ P)) → Q w
elimW Q m (sup (s , f)) = m (s , f) (elimW Q m ∘ f)

record M (SP : Cont) : Set where
  coinductive
  field
    inf : ⟦ SP ⟧ (M SP)
open M    

M₁ : SP →ᶜ TQ → M SP → M TQ
inf (M₁ (g ◃ h) msp) with inf msp
... | s , f = g s , λ q → M₁ (g ◃ h) (f (h s q))

module _ (X : Set) (SP : Cont) (g : X → ⟦ SP ⟧ X) where
  
  coitM : X → M SP
  inf (coitM x) with g x
  ... | s , f = s , coitM ∘ f

module _ (X : Set) (SP : Cont) (g : X → ⟦ SP ⟧ (M SP ⊎ X)) where

  corecM : X → M SP
  inf (corecM x) with g x
  ... | s , f = s , λ p → case f p of
    λ{ (inj₁ m) → m ; (inj₂ x') → corecM x' }

shape : {S : Set} {P : S → Set} → M (S ◃ P) → S
shape m with inf m
... | s , f = s

pos : {S : Set} {P : S → Set} (m : M (S ◃ P)) → P (shape m) → M (S ◃ P)
pos m p with inf m
... | s , f = f p

record _≈M_ (m₁ m₂ : M SP) : Set where
  coinductive
  open Cont SP
  field
    s≡ : shape m₁ ≡ shape m₂
    f≡ : (p₁ : P (shape m₁)) → pos m₁ p₁ ≈M pos m₂ (subst P s≡ p₁)

postulate
  coelimM : {m₁ m₂ : M SP}
    → m₁ ≈M m₂ → m₁ ≡ m₂

open import Data.Nat

{-
record CoVec (A : Set) : ℕ → Set where
  coinductive
  destructor
    hd : {n : ℕ} → CoVec A (suc n) → A
    tl : {n : ℕ} → CoVec A (suc n) → CoVec A n
-}

