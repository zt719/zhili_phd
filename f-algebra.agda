{-# OPTIONS --guardedness #-}

module F-Algebra where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Function.Base
open import Relation.Binary.PropositionalEquality

Tℕ : Set → Set
Tℕ A = ⊤ ⊎ A

Tℕ₁ : {X Y : Set} → (X → Y) → Tℕ X → Tℕ Y
Tℕ₁ f (inj₁ tt) = inj₁ tt
Tℕ₁ f (inj₂ x) = inj₂ (f x)

Itℕ : {X : Set} → (Tℕ X → X) → ℕ → X
Itℕ f zero = f (inj₁ tt)
Itℕ f (suc n) = f (inj₂ (Itℕ f n))

ℕ-alg : Tℕ ℕ → ℕ
ℕ-alg (inj₁ tt) = zero
ℕ-alg (inj₂ n) = suc n

initial-ℕ-alg : {X : Set} (f : Tℕ X → X) (a : Tℕ ℕ)
  → Itℕ f (ℕ-alg a) ≡ f (Tℕ₁ (Itℕ f) a)
initial-ℕ-alg f (inj₁ tt) = refl
initial-ℕ-alg f (inj₂ n) = refl

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : ⊤ ⊎ ℕ∞
open ℕ∞

Coitℕ∞ : {X : Set} → (X → Tℕ X) → X → ℕ∞
pred∞ (Coitℕ∞ f x) with f x
... | inj₁ tt = inj₁ tt
... | inj₂ x′ = inj₂ (Coitℕ∞ f x′)

ℕ∞-coalg : ℕ∞ → Tℕ ℕ∞
ℕ∞-coalg n = pred∞ n

terminal-ℕ∞-coalg : {X : Set} (f : X → Tℕ X) (x : X)
  → ℕ∞-coalg (Coitℕ∞ f x) ≡ Tℕ₁ (Coitℕ∞ f) (f x)
terminal-ℕ∞-coalg f x with f x
... | inj₁ tt = refl
... | inj₂ x′ = refl

TL : (Set → Set) → Set → Set
TL F A = ⊤ ⊎ A × F A

TL₁ : {F G : Set → Set}
  → ((X : Set) → F X → G X)
  → (X : Set) → TL F X → TL G X
TL₁ α X (inj₁ tt) = inj₁ tt
TL₁ α X (inj₂ (x , xs)) = inj₂ (x , α X xs)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

List₁ : {X Y : Set} → (X → Y) → List X → List Y
List₁ f [] = []
List₁ f (x ∷ xs) = f x ∷ List₁ f xs

It-List : {F : Set → Set}
  → ((X : Set) → TL F X → F X)
  → (X : Set) → List X → F X
It-List α X [] = α X (inj₁ tt)
It-List α X (x ∷ xs) = α X (inj₂ (x , It-List α X xs)) 

List-alg : (X : Set) → TL List X → List X
List-alg X (inj₁ tt) = []
List-alg X (inj₂ (x , xs)) = x ∷ xs

initial-List-alg : {F : Set → Set}
  → (α : (X : Set) → TL F X → F X) (X : Set) (lxs : TL List X)
  → It-List α X (List-alg X lxs) ≡ α X (TL₁ (It-List α) X lxs)
initial-List-alg α X (inj₁ tt) = refl
initial-List-alg α X (inj₂ lxs′) = refl

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

TB : (Set → Set) → Set → Set
TB F A = A × F (F A)

TB₁ : {F G : Set → Set}
  → {G₁ : {X Y : Set} → (X → Y) → G X → G Y}
  → ((X : Set) → F X → G X)
  → (X : Set) → TB F X → TB G X
TB₁ {F} {G} {G₁} α X (x , ffx) = x , G₁ (α X) (α (F X) ffx)

{-# TERMINATING #-}
Coit-Bush : {F : Set → Set}
  → {F₁ : {X Y : Set} → (X → Y) → F X → F Y}
  → ((X : Set) → F X → TB F X)
  → (X : Set) → F X → Bush X
head (Coit-Bush α X fx) = proj₁ (α X fx)
tail (Coit-Bush {F₁ = F₁} α X fx)
  = Coit-Bush {F₁ = F₁} α (Bush X) (F₁ (Coit-Bush {F₁ = F₁} α X) (proj₂ (α X fx)))

Bush-coalg : (X : Set) → Bush X → TB Bush X
Bush-coalg X bx = head bx , tail bx

postulate
  Bush₁-id : {X : Set} (bx : Bush X)
    → Bush₁ (id {A = X}) bx ≡ id {A = Bush X} bx
    
  Bush₁-∘ : {X Y Z : Set} {f : Y → Z} {g : X → Y}
    → (bx : Bush X) → Bush₁ (f ∘ g) bx ≡ Bush₁ f (Bush₁ g bx)

terminal-Bush-coalg : {F : Set → Set}
  → {F₁ : {X Y : Set} → (X → Y) → F X → F Y}
  → (α : (X : Set) → F X → TB F X) (X : Set) (fx : F X)
  → Bush-coalg X (Coit-Bush {F₁ = F₁} α X fx) ≡ TB₁ {G₁ = Bush₁} (Coit-Bush {F₁ = F₁} α) X (α X fx)
terminal-Bush-coalg α X fx with α X fx
... | x , ffx = cong₂ _,_ refl {!!}

------------------------------------------------------------------------------------------

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

ℕ-Cont : Cont
ℕ-Cont = S ◃ P
  where
  S : Set
  S = ⊤ ⊎ ⊤

  P : S → Set
  P (inj₁ tt) = ⊥
  P (inj₂ tt) = ⊤

record ⟦_⟧ (cont : Cont) (A : Set) : Set where
  constructor _,_
  open Cont cont
  field
    s : S
    p : P s → A

Tℕ′ : Set → Set
Tℕ′ = ⟦ ℕ-Cont ⟧

Tℕ′₁ : {X Y : Set} → (X → Y) → Tℕ′ X → Tℕ′ Y
Tℕ′₁ f (inj₁ tt , p) = inj₁ tt , λ ()
Tℕ′₁ f (inj₂ tt , p) = inj₂ tt , f ∘ p

record Cont₂ : Set₁ where
  constructor _◃_◃_◃_
  inductive
  field
    S : Set
    Pf : S → Set
    Pa : S → Set
    Rf : (s : S) → Pf s → Cont₂

{-
H   F A = A × F (H′ F A)
H′  F A = F (H′′ F A)
H′′ F A = A
-}

Bush-Cont : Cont₂
Bush-Cont = ⊤ ◃ (λ _ → ⊤) ◃ (λ _ → ⊤) ◃ λ s pf → Bush-Cont′
  where
  End : Cont₂
  End = ⊥ ◃ (λ ()) ◃ (λ ()) ◃ (λ ())
  
  Bush-Cont′′ : Cont₂
  Bush-Cont′′ = ⊤ ◃ (λ _ → ⊥) ◃ (λ _ → ⊤) ◃ λ s pf → End

  Bush-Cont′ : Cont₂
  Bush-Cont′ = ⊤ ◃ (λ _ → ⊤) ◃ (λ _ → ⊥) ◃ λ s pf → Bush-Cont′′

{-# NO_POSITIVITY_CHECK #-}
record ⟦_⟧₂ (cont₂ : Cont₂) (F : Set → Set) (A : Set) : Set where
  coinductive
  open Cont₂ cont₂
  field
    s : S
    pf : (p : Pf s) → F (⟦ Rf s p ⟧₂ F A)
    pa : (a : Pa s) → A

TB′ : (Set → Set) → Set → Set
TB′ = ⟦ Bush-Cont ⟧₂

------------------------------------------------------------------------------------------

T× : Set → Set → Set
T× A B = A × B

T×₁ : {X Y : Set} → (X → Y)
  → (Z : Set) → T× X Z → T× Y Z
T×₁ f Z (x , z) = f x , z

Tf : (Set → Set) → Set
Tf F = F ⊤

Tf₁ : {F G : Set → Set}
  → ((X : Set) → F X → G X)
  → Tf F → Tf G
Tf₁ α x = α ⊤ x

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty
  
⟦_⟧ty : Ty → Set₁
⟦ set ⟧ty = Set
⟦ A ⇒ B ⟧ty = ⟦ A ⟧ty → ⟦ B ⟧ty

Fℕ′ : ⟦ set ⇒ set ⟧ty
Fℕ′ A = ⊤ ⊎ A
