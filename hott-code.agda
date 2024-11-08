module HoTT-Code where

open import Relation.Binary.PropositionalEquality
open import Function.Base
open import Data.Nat
open import Data.Product

variable
  A : Set

ind≡ : (C : (x y : A) → x ≡ y → Set)
  → ((x : A) → C x x refl)
  → (x y : A) (p : x ≡ y)
  → C x y p
ind≡ C c x .x refl = c x

ind≡′ : (a : A) (C : (x : A) → a ≡ x → Set)
  → C a refl
  → (x : A) (p : a ≡ x)
  → C x p
ind≡′ a C c .a refl = c

inv : (x y : A) → x ≡ y → y ≡ x
inv = ind≡ D d
  where
  D : (x y : A) → x ≡ y → Set
  D x y p = y ≡ x

  d : (x : A) → x ≡ x
  d x = refl

f : (x y : A) → x ≡ y → (z : A) → y ≡ z → x ≡ z
f = ind≡ D (ind≡ E e)
  where
  D : (x y : A) → x ≡ y → Set
  D {A} x y p = (z : A) → y ≡ z → x ≡ z

  E : (x z : A) → x ≡ z → Set
  E x z q = x ≡ z

  e : (x : A) → E x x refl
  e x = refl

comp : {A : Set} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
comp {A} {x} {y} {z} q p = f x y p z q

_∙_ = trans

P1 : (x y : A) (p : x ≡ y) → p ≡ p ∙ refl
P1 x y p = ind≡ D d x y p
  where
  D : (x y : A) → x ≡ y → Set
  D x y p = p ≡ p ∙ refl

  d : (x : A) → D x x refl
  d x = refl

module Loop-Space where

  Ω : (A : Set) (a : A) → Set
  Ω A a = a ≡ a

  Ω² : (A : Set) (a : A) → Set
  Ω² A a = Ω (Ω A a) refl

  Eck-Hil : {A : Set} {a : A} (α β : Ω² A a)
    → α ∙ β ≡ β ∙ α
  Eck-Hil refl refl = refl

module Iterated-Loop-Space where

  U∙ : Set₁
  U∙ = Σ[ A ∈ Set ] A

  Ω : U∙ → U∙
  Ω (A , a) = (a ≡ a) , refl

  Ωⁿ : ℕ → U∙ → U∙
  Ωⁿ zero (A , a) = A , a
  Ωⁿ (suc n) (A , a) = Ωⁿ n (Ω (A , a))

tr : {A : Set} (P : A → Set)
  → {x y : A} (p : x ≡ y) → P x → P y
tr {A} P {x} {y} = ind≡ D d x y
  where
  D : (x y : A) → x ≡ y → Set
  D x y p = P x → P y

  d : (x : A) → D x x refl
  d x = id

lift : {A : Set} (P : A → Set)
  → {x y : A} (p : x ≡ y) (u : P x)
  → (x , u) ≡ (y , tr P p u)
lift {A} P {x} {y} = ind≡ D d x y
  where
  D : (x y : A) → x ≡ y → Set
  D x y p = (u : P x) → (x , u) ≡ (y , tr P p u)

  d : (x : A) → D x x refl
  d x = λ u → refl


apd : {A : Set} (P : A → Set)
  → (f : (x : A) → P x) {x y : A} (p : x ≡ y)
  → tr P p (f x) ≡ f y
apd {A} P f {x} {y} = ind≡ D d x y
  where
  D : (x y : A) → x ≡ y → Set
  D x y p = tr P p (f x) ≡ f y

  d : (x : A) → D x x refl
  d x = refl

ap-∙ : {A : Set} (P : A → Set)
  (x y z : A) (p : x ≡ y) (q : y ≡ z)
  (u : P x) → tr P q (tr P p u) ≡ tr P (p ∙ q) u
ap-∙ {A} P x .x .x refl refl u = refl

