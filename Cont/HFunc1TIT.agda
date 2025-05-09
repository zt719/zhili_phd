{-# OPTIONS --cubical --type-in-type #-}

module Cont.HFunc1TIT where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Data.Unit renaming (Unit to ⊤)

{- Category, Functor, Natural Transformation -}

record Cat (Obj : Type) : Type where
  infixr 9 _∘_
  field
    Hom : Obj → Obj → Type
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    ass : ∀ {W X Y Z} (f : Hom X W) (g : Hom Y X) (h : Hom Z Y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

record Func {A B : Type} (ℂ : Cat A) (𝔻 : Cat B) (F : A → B) : Type where
  open Cat
  field
    F₁ : ∀ {X Y} → Hom ℂ X Y → Hom 𝔻 (F X) (F Y)
    F-id : ∀ {X} → F₁ {X} (ℂ .id) ≡ 𝔻 .id
    F-∘ : ∀ {X Y Z} (f : Hom ℂ Y Z) (g : Hom ℂ X Y)
          → F₁ (ℂ ._∘_ f g ) ≡ 𝔻 ._∘_ (F₁ f) (F₁ g)

record Nat {A B : Type} (ℂ : Cat A) (𝔻 : Cat B)
  (F G : A → B) (FF : Func ℂ 𝔻 F) (GG : Func ℂ 𝔻 G) : Type where
  open Cat
  open Func
  field
    η : ∀ X → Hom 𝔻 (F X) (G X)
    nat : ∀ {X Y} (f : Hom ℂ X Y)
      → 𝔻 ._∘_ (GG .F₁ f) (η X) ≡ 𝔻 ._∘_ (η Y) (FF .F₁ f)

postulate
  Nat≡ : {A B : Type} {ℂ : Cat A} {𝔻 : Cat B} {F G : A → B}
    → {FF : Func ℂ 𝔻 F} {GG : Func ℂ 𝔻 G}
    → {α β : Nat ℂ 𝔻 F G FF GG}
    → α .Nat.η ≡ β .Nat.η → α ≡ β

{- Syntax -}

infixr 20 _⇒_
data Ty : Type where
  * : Ty
  _⇒_ : Ty → Ty → Ty

data TTy : Type

data Tel : Type

data TTy where
  _⇒* : Tel → TTy

infixr 5 _◁_
data Tel where
  •   : Tel
  _◁_ : TTy → Tel → Tel 

TTy2Ty : TTy → Ty
TTy2Ty (ts ⇒*) = Tel2Ty ts
  where
  Tel2Ty : Tel → Ty
  Tel2Ty • = *
  Tel2Ty (t ◁ ts) = Tel2Ty ts ⇒ TTy2Ty t

Ty2TTy : Ty → TTy
Ty2TTy * = • ⇒*
Ty2TTy (A ⇒ B) with Ty2TTy B
... | TelB ⇒* = (Ty2TTy A ◁ TelB) ⇒*
