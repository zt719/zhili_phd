{-# OPTIONS --cubical --guardedness #-}

module Equiv where

open import Function.Base
open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Equiv.Base

variable
  ℓ ℓ' : Level
  A B : Type ℓ

{- Homotopy -}

infix  0 _~_

_~_ : {A : Type ℓ} {B : Type ℓ'} (f g : A → B) → Type (ℓ-max ℓ ℓ')
f ~ g = (x : _) → f x ≡ g x

{- Naturality of Homotopy -}


{-
nat-htpy : {A : Type ℓ} {B : Type ℓ'}
  {f g : A → B} (α : f ~ g)
  {x y : A} (p : x ≡ y)
  → α x ∙ cong g p ≡ cong f p ∙ α y
nat-htpy α p i j = {!!}
-}

{-
nat-htpy : {A : Type ℓ} (f : A → A) (α : f ~ id) (x : A)
  → α (f x) ≡ cong f (α x)
nat-htpy f α x i j = {!!}
  where
  lem : cong f (α x) ∙ α x ≡ α (f x) ∙ α x
  lem i j = {!!}
-}

{- Quasi-inversable -}

record isQinv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    g : B → A
    α : f ∘ g ≡ id    
    β : g ∘ f ≡ id

{- Isomorphism -}

Iso : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
Iso A B = Σ (A → B) isQinv

_≅_ = Iso

{- Bi-invertable -}

record isBiinv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    g : B → A
    α : f ∘ g ≡ id
    h : B → A
    β : h ∘ f ≡ id

{- Fiber -}

fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A → B) → B → Type (ℓ-max ℓ ℓ')
fiber {A = A} f b = Σ[ a ∈ A ] f a ≡ b

{- Contractible fiber -}

record isContrFiber {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    proof : (b : B) → isContr (fiber f b)

{- Cong -}

congSq : {A : Type ℓ} {B : Type ℓ'} {x y : A} {p q : x ≡ y}
  → (f : A → B) → p ≡ q → cong f p ≡ cong f q
congSq f α i j = f (α i j)

{- Half Adjoint Equivalence -}

record isHae {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    g : B → A
    η : g ∘ f ≡ id
    ε : f ∘ g ≡ id    
    τ : cong (f ∘_) η ≡ cong (_∘ f) ε

  --            refl i
  -- f (g (f x)   →  f (g (f x)
  --  ↓ f (η j x)     ↓ ε j (f x)
  -- f x          →  f x
  --            refl i

--  ν : cong (g ∘_) ε ≡ cong (_∘ g) η
--  ν i j y = {!!}

  --            refl i
  -- g (f (g x))  →  g (f (g x)
  --  ↓ η j (g x)     ↓ g (ε j x)
  -- g x          →  g x
  --            refl i

  -- 


record CoindEquiv {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  coinductive
  field
    f : A → B
    g : B → A
    proof : (a : A) (b : B) → CoindEquiv (f a ≡ b) (a ≡ g b)

record isCoindEquiv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) : Type (ℓ-max ℓ ℓ') where
  coinductive
  field
    g : B → A
    ff : (a : A) (b : B) → Σ[ ff ∈ (f a ≡ b → a ≡ g b) ] isCoindEquiv ff

-------

{-
iso→biinv : {A : Type ℓ} {B : Type ℓ} (f : A → B) → isQinv f → isBiinv f
iso→biinv f record { g = g ; α = α ; β = β }
  = record { g = g ; α = α ; h = g ; β = β }

biinv→iso : {A : Type ℓ} {B : Type ℓ} (f : A → B) → isBiinv f → isQinv f
biinv→iso f record { g = g ; α = α ; h = h ; β = β }
  = record { g = g ; α = α ; β = β' }
  where
  γ : g ~ h
  γ x = sym (β (g x)) ∙ cong h (α x)

  β' : g ∘ f ~ id
  β' x = γ (f x) ∙ β x

-------

data S¹ : Type where
  base : S¹
  loop : base ≡ base

idS¹-isQinv : isQinv (id {A = S¹})
idS¹-isQinv = record { g = id ; α = λ x → refl ; β = λ x → refl }

module _ where

  g : S¹ → S¹
  g base = base
  g (loop i) = (loop ∙ loop) i

  idS¹-isQinv' : isQinv (id {A = S¹})
  idS¹-isQinv' = record { g = g ; α = {!!} ; β = {!!} }


idS¹-isContrFiber : isContrFiber (id {A = S¹})
idS¹-isContrFiber = record { proof = proof }
  where
  proof : (b : S¹) → isContr (fiber id b)
  proof b = (b , refl) , λ{ (b' , p) i → p (~ i) , (λ j → p (~ i ∨ j)) }

-}
