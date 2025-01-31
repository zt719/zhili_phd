module Cont.Monad where

open import Function.Base
open import Relation.Binary.PropositionalEquality

record Monad : Set₁ where
  field
    M : Set → Set
    M₁ : ∀ {X Y} → (X → Y) → M X → M Y
    M-id : ∀ {X} → M₁ {X} id ≡ id
    M-∘ : ∀ {X Y Z} (f : Y → Z) (g : X → Y)
        → M₁ (f ∘ g) ≡ M₁ f ∘ M₁ g
    η : ∀ {X} → X → M X
    μ : ∀ {X} → M (M X) → M X
    idl : ∀ {X} → μ ∘ η ≡ id {A = M X}
    idr : ∀ {X} → μ ∘ M₁ η ≡ id {A = M X}
    ass : ∀ {X} → μ ∘ μ ≡ μ ∘ M₁ (μ {X})


comp-m : Monad → Monad → Monad
comp-m
  record { M = M ; M₁ = M₁ ; M-id = M-id ; M-∘ = M-∘ ; η = η ; μ = μ ; idl = idl ; idr = idr ; ass = ass }
  record { M = N ; M₁ = N₂ ; M-id = N-id₁ ; M-∘ = N-∘₁ ; η = η₁ ; μ = μ₁ ; idl = idl₁ ; idr = idr₁ ; ass = ass₁ } = record
   { M = M ∘ N
   ; M₁ = {!!}
   ; M-id = {!!}
   ; M-∘ = {!!}
   ; η = η ∘ η₁
   ; μ = λ mnmnx → {!!}
   ; idl = {!!}
   ; idr = {!!}
   ; ass = {!!}
   }
