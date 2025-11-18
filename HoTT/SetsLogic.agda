{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude

{- Propositional Truncation (Squash Type) -}

variable A B : Type

data ∥_∥ (A : Type) : Type where
  ∣_∣  : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y

rec∥-∥ : (B : Type)
  (b : (a : A) → B)
  (f : (b₁ b₂ : B) → b₁ ≡ b₂)
  → ∥ A ∥ → B
rec∥-∥ B b f ∣ x ∣ = b x
rec∥-∥ B b f (squash x y i) = f (rec∥-∥ B b f x) (rec∥-∥ B b f y) i

ind∥-∥ : (P : ∥ A ∥ → Type)
  (b : (x : A) → P ∣ x ∣)
  (f : (x y : ∥ A ∥) (px : P x) (py : P y) → PathP (λ i → P (squash x y i)) px py)
  (x : ∥ A ∥) → P x
ind∥-∥ P b f ∣ x ∣ = b x
ind∥-∥ P b f (squash x y i)
  = f x y (ind∥-∥ P b f x) (ind∥-∥ P b f y) i

{- Type Theoretical Choice -}
  
TTC : {X : Type} {A : X → Type} {P : (x : X) → A x → Type}
  → ((x : X) → Σ[ a ∈ A x ] P x a) → Σ[ g ∈ ((x : X) → A x) ] ((x : X) → P x (g x))
TTC h = (λ x → let (a , p) = h x in a) , (λ x → let (a , p) = h x in p)

TTC⁻ : {X : Type} {A : X → Type} {P : (x : X) → A x → Type}
  → (Σ[ g ∈ ((x : X) → A x) ] ((x : X) → P x (g x))) → (x : X) → Σ[ a ∈ A x ] P x a
TTC⁻ (g , f) x = g x , f x

{- Axiom of Choice -}

postulate
  AC⁻¹ : {X : Type} {A : X → Type} {P : (x : X) → A x → Type}
    (setX : isSet X)
    (setA : (x : X) → isSet (A x))
    (propP : (x : X) (a : A x) → isProp (P x a))
    → ((x : X) → ∥ Σ[ a ∈ A x ] P x a ∥)
    → ∥ Σ[ g ∈ ((x : X) → A x) ] ((x : X) → P x (g x)) ∥

postulate
  AC : {X : Type} {Y : X → Type}
    (setX : isSet X)
    (setY : (x : X) → isSet (Y x))
    → ((x : X) → ∥ Y x ∥) → ∥ ((x : X) → Y x) ∥
