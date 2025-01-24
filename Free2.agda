{-# OPTIONS --cubical #-}

module Free2 where

open import Function.Base
open import Cubical.Foundations.Prelude hiding (_◁_)

record Func : Type₁ where
  field
    F : Type → Type
    F₁ : ∀ {X Y} → (X → Y) → F X → F Y
    F-id : ∀ {X} → F₁ {X} id ≡ id
    F-∘ : ∀ {X Y Z} (f : Y → Z) (g : X → Y)
        → F₁ (f ∘ g) ≡ F₁ f ∘ F₁ g

record Monad : Type₁ where
  field
    M : Type → Type
    M₁ : ∀ {X Y} → (X → Y) → M X → M Y
    M-id : ∀ {X} → M₁ {X} id ≡ id
    M-∘ : ∀ {X Y Z} (f : Y → Z) (g : X → Y)
        → M₁ (f ∘ g) ≡ M₁ f ∘ M₁ g
    M-η : ∀ {X} → X → M X
    M-μ : ∀ {X} → M (M X) → M X
    M-idl : ∀ {X} → M-μ ∘ M-η ≡ id {A = M X}
    M-idr : ∀ {X} → M-μ ∘ M₁ M-η ≡ id {A = M X}
    M-ass : ∀ {X} → M-μ ∘ M-μ ≡ M-μ ∘ M₁ (M-μ {X})

{-# NO_POSITIVITY_CHECK #-}
data Free (F : Type → Type) (A : Type) : Type where
  Var : A → Free F A
  Op  : F (Free F A) → Free F A

module _ (FF : Func) where

  open Func FF

  variable A B C : Set

  {-# TERMINATING #-}
  Free₁ : (A → B) → Free F A → Free F B
  Free₁ f (Var a) = Var (f a)
  Free₁ f (Op op) = Op (F₁ (Free₁ f) op)
  
  {-# TERMINATING #-}
  Free-id : Free₁ (id {A = A}) ≡ id
  Free-id i (Var a) = Var a
  Free-id i (Op op) = Op ((cong F₁ Free-id ∙ F-id) i op)

  {-# TERMINATING #-}
  Free-∘ : (f : B → C) (g : A → B) → Free₁ (f ∘ g) ≡ Free₁ f ∘ Free₁ g
  Free-∘ f g i (Var a) = Var (f (g a))
  Free-∘ f g i (Op op) = Op ((cong F₁ (Free-∘ f g) ∙ F-∘ (Free₁ f) (Free₁ g)) i op)

  Free-η : A → Free F A
  Free-η = Var

  {-# TERMINATING #-}
  Free-μ : Free F (Free F A) → Free F A
  Free-μ (Var a) = a
  Free-μ (Op op) = Op (F₁ Free-μ op)

  Free-idl : Free-μ ∘ Free-η ≡ id {A = Free F A}
  Free-idl = refl

  {-# TERMINATING #-}
  Free-idr : Free-μ ∘ Free₁ Free-η ≡ id {A = Free F A}
  Free-idr i (Var a) = Var a
  Free-idr i (Op op) = Op ((sym (F-∘ Free-μ (Free₁ Free-η)) ∙ cong F₁ Free-idr ∙ F-id) i op)

  {-# TERMINATING #-}
  Free-ass : Free-μ ∘ Free-μ ≡ Free-μ ∘ Free₁ (Free-μ {A})
  Free-ass i (Var a) = Free-μ a
  Free-ass i (Op op) = Op ((sym (F-∘ Free-μ Free-μ) ∙
                             cong F₁ Free-ass ∙ F-∘ Free-μ (Free₁ Free-μ))
                            i op)

  {-# TERMINATING #-}
  fold : (F A → A) → Free F A → A
  fold alg (Var a) = a
  fold alg (Op op) = alg (F₁ (fold alg) op)

module _ (LL RR : Func) where

  open Func LL renaming (F to L; F₁ to L₁; F-id to L-id; F-∘ to L-∘)
  open Func RR renaming (F to R; F₁ to R₁; F-id to R-id; F-∘ to R-∘)

  data _+_ (L R : Type → Type) (A : Type) : Type where
    Inl : L A → (L + R) A
    Inr : R A → (L + R) A

  _+₁_ : (A → B) → (L + R) A → (L + R) B
  _+₁_ f (Inl x) = Inl (L₁ f x)
  _+₁_ f (Inr y) = Inr (R₁ f y)

{-
  +-id : (L +₁ RR) (id {A = A}) ≡ id {A = (L + R) A}
  +-id i (Inl x) = Inl (L-id i x)
  +-id i (Inr y) = Inr (R-id i y)
-}
{-
  +-∘ : (f : B → C) (g : A → B) → +₁ {LL} {_} {RR} (f ∘ g) ≡ +₁ f ∘ +₁ g
  +-∘ f g i (Inl x) = Inl (L-∘ f g i x)
  +-∘ f g i (Inr y) = Inr (R-∘ f g i y)
-}

-- State s k = Get (s -> k) | Put s k

data State (S K : Set) : Set where
  Get : (S -> K) → State S K
  Put : S -> K -> State S K

module _ (S : Set) where

  State₁ : {A B : Set} → (A → B) → State S A → State S B
  State₁ f (Get k) = Get (f ∘ k)
  State₁ f (Put s a) = Put s (f a)

  State-id : {A : Set} → State₁ (id {A = A}) ≡ id
  State-id i (Get k) = Get k
  State-id i (Put s a) = Put s a

  State-∘ : {A B C : Set} (f : B → C) (g : A → B)
    → State₁ (f ∘ g) ≡ State₁ f ∘ State₁ g
  State-∘ f g i (Get k) = Get (f ∘ g ∘ k)
  State-∘ f g i (Put s a) = Put s (f (g a))
