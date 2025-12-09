{-# OPTIONS --guardedness --cubical #-}

open import Cubical.Foundations.Prelude

{- Interval -}

data 𝕀 : Type where
  𝟘 : 𝕀
  𝟙 : 𝕀
  seg : Path 𝕀 𝟘 𝟙

rec𝕀 : (B : Type)
  (b₀ : B)
  (b₁ : B)
  (s : b₀ ≡ b₁)
  → 𝕀 → B
rec𝕀 B b₀ b₁ s 𝟘 = b₀
rec𝕀 B b₀ b₁ s 𝟙 = b₁
rec𝕀 B b₀ b₁ s (seg i) = s i

ind𝕀 : (P : 𝕀 → Type)
  (p₀ : P 𝟘)
  (p₁ : P 𝟙)
  (ps : PathP (λ i → P (seg i)) p₀ p₁)
  (𝕚 : 𝕀) → P 𝕚
ind𝕀 P p₀ p₁ ps 𝟘 = p₀
ind𝕀 P p₀ p₁ ps 𝟙 = p₁
ind𝕀 P p₀ p₁ ps (seg i) = ps i

{- Circle -}

data S¹ : Type where
  base : S¹
  loop : base ≡ base

recS¹ : (B : Type)
  (b : B)
  (l : b ≡ b)
  → S¹ → B
recS¹ B b l base = b
recS¹ B b l (loop i) = l i

indS¹ : (P : S¹ → Type)
  (pb : P base)
  (pl : PathP (λ i → P (loop i)) pb pb)
  (s : S¹) → P s
indS¹ P pb pl base = pb
indS¹ P pb pl (loop i) = pl i

{- Suspension -}

data Susp (A : Type) : Type where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

recSusp : {A : Type} (B : Type)
  (n : B)
  (s : B)
  (m : (a : A) → n ≡ s)
  → Susp A → B
recSusp B n s m north = n
recSusp B n s m south = s
recSusp B n s m (merid a i) = m a i

indSusp : {A : Type} (P : Susp A → Type)
  (pn : P north)
  (ps : P south)
  (pm : (a : A) → PathP (λ i → P (merid a i)) pn ps)
  (s : Susp A) → P s
indSusp P pn ps pm north = pn
indSusp P pn ps pm south = ps
indSusp P pn ps pm (merid a i) = pm a i

{- Set Quotient -}

data _/_ (A : Type)  (R : A → A → Type) : Type where
  [_] : (a : A) → A / R
  eq/ : (a b : A) (r : R a b) → [ a ] ≡ [ b ]
  squash/ : (x y : A / R) (p q : x ≡ y) → p ≡ q

{- Integer -}

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

_~_ : ℕ × ℕ → ℕ × ℕ → Type
(a , b) ~ (c , d) = a + d ≡ b + c

ℤ : Type
ℤ = (ℕ × ℕ) / _~_

{- Torus -}

data T² : Type where
  point : T²
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

module S¹≃Susp-Bool where

  open import Cubical.Data.Bool
  open import Function.Base

  to : S¹ → Susp Bool
  to base = north
  to (loop i) = (merid true ∙ sym (merid false)) i

  from : Susp Bool → S¹
  from north = base
  from south = base
  from (merid false i) = base
  from (merid true i) = loop i

--  hSquareComp : Path

  to∘from : to ∘ from ≡ id
  to∘from i north = north
  to∘from i south = merid false i
  to∘from i (merid false j) = merid false (i ∧ j)
  to∘from i (merid true j) = {!!}
    where
    square1 : Path (north ≡ south) (merid true) (merid true)
    square1 = refl

    square2 : PathP (λ i → refl i ≡ merid false i) (sym (merid false)) (refl {x = south})
    square2 i j = sym (merid false) (~ i ∧ j)
