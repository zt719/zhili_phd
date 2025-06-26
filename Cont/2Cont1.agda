{-# OPTIONS --type-in-type #-}

module Cont.2Cont1 where

record Cat : Set where
  field
    Obj : Set
    Hom : Obj → Obj → Set
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    {- +laws -}

id' : {X : Set} → X → X
id' x = x

_∘'_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(f ∘' g) x = f (g x)

module _ (ℂ : Cat) where
  open Cat ℂ

  {- Container -}
  infix  0 _◃_
  record Cont : Set₁ where
    constructor _◃_
    field
      S : Set
      P : S → Obj

  private variable SP TQ : Cont

  {- Container Hom -}
  record ContHom (SP TQ : Cont) : Set where
    constructor _◃_
    open Cont SP
    open Cont TQ renaming (S to T; P to Q)
    field
      f : S → T
      g : (s : S) → Hom (Q (f s)) (P s)

  CONT : Cat
  CONT .Obj = Cont
  CONT .Hom = ContHom
  CONT .id = id' ◃ λ s → id
  CONT ._∘_ (f ◃ g) (h ◃ k) = f ∘' h ◃ λ s → k s ∘ g (h s)

module _ {ℂ : Cat} where

  open Cat ℂ

  {- Container Extension Functor -}
  record ⟦_⟧ (SP : Cont ℂ) (X : Obj) : Set where
    constructor _,_
    open Cont SP
    field
      s : S
      p : Hom (P s) X

  {- Functoriality -}
  ⟦_⟧₁ : (SP : Cont ℂ) {X Y : Obj} → Hom X Y → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
  ⟦ SP ⟧₁ f (s , p) = s , (f ∘ p)
  {-# INLINE ⟦_⟧₁ #-}

  {- Naturality -}
  ⟦_⟧Hom : {SP TQ : Cont ℂ} → ContHom ℂ SP TQ → (X : Obj) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
  ⟦ f ◃ g ⟧Hom X (s , p) = f s , (p ∘ g s)


SET : Cat
SET = record
  { Obj = Set
  ; Hom = λ X Y → X → Y
  ; id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  }

1Cont : Set
1Cont = Cont SET

1ContHom : 1Cont → 1Cont → Set
1ContHom = ContHom SET

1⟦_⟧ : 1Cont → Set → Set
1⟦_⟧ = ⟦_⟧

1⟦_⟧₁ : (SP : 1Cont) → {X Y : Set} → (X → Y) → 1⟦ SP ⟧ X → 1⟦ SP ⟧ Y
1⟦_⟧₁ = ⟦_⟧₁

1⟦_⟧Hom : ∀ {SP TQ} → 1ContHom SP TQ → ∀ X → 1⟦ SP ⟧ X → 1⟦ TQ ⟧ X
1⟦_⟧Hom = ⟦_⟧Hom

record 2Cont : Set

record 2ContHom (C D : 2Cont) : Set

2CONT : Cat

record 2Cont where
  inductive
  field
    S : Set
    P₀ : S → Cont 2CONT
    P₁ : S → Set    

record 2ContHom SPP TQQ where
  inductive
  eta-equality
  open 2Cont SPP
  open 2Cont TQQ renaming (S to T; P₀ to Q₀; P₁ to Q₁)
  field
    f : S → T
    g₀ : (s : S) → ContHom 2CONT (Q₀ (f s)) (P₀ s)
    g₁ : (s : S) → Q₁ (f s) → P₁ s

open Cat

{-# TERMINATING #-}
2CONT = record
  { Obj = 2Cont
  ; Hom = 2ContHom
  ; id = record
    { f = id'
    ; g₀ = λ s → id' ◃ λ s₁ → 2CONT .id
    ; g₁ = λ s → id'
    }
  ; _∘_ = λ δ γ → record
    { f = δ .2ContHom.f ∘' γ .2ContHom.f
    ; g₀ = λ s → γ .2ContHom.g₀ s .ContHom.f ∘' (δ .2ContHom.g₀ (γ .2ContHom.f s) .ContHom.f)
         ◃ λ s₁ → 2CONT ._∘_ (δ .2ContHom.g₀ (γ .2ContHom.f s) .ContHom.g s₁) (γ .2ContHom.g₀ s .ContHom.g (δ .2ContHom.g₀ (γ .2ContHom.f s) .ContHom.f s₁))
    ; g₁ = λ s → γ .2ContHom.g₁ s ∘' (δ .2ContHom.g₁ (γ .2ContHom.f s))
    }
  }

{-# NO_POSITIVITY_CHECK #-}
record 2⟦_⟧ (C : 2Cont) (F : 1Cont) (X : Set) : Set where
  inductive
  eta-equality
  open 2Cont C
  field
    s : S
    k₀ : (p : P₀ s .Cont.S) → ⟦ F ⟧ (2⟦ P₀ s .Cont.P p ⟧ F X)
    k₁ : P₁ s → X

{-# TERMINATING #-}
2⟦_⟧₁ : (C : 2Cont)
  → {F G : 1Cont} → 1ContHom F G
  → {X Y : Set} → (X → Y)
  → 2⟦ C ⟧ F X → 2⟦ C ⟧ G Y
2⟦ C ⟧₁ {F} {G} α {X} {Y} f record { s = s ; k₀ = k₀ ; k₁ = k₁ } =
  record
  { s = s
  ; k₀ = λ p → ⟦ α ⟧Hom (2⟦ (P₀ C s) .P p ⟧ G Y) (⟦ F ⟧₁ (2⟦ (P₀ C s) .P p ⟧₁ α f) (k₀ p))
  ; k₁ = f ∘' k₁
  }
  where
    open 2Cont
    open Cont

{-# TERMINATING #-}
2⟦_⟧Hom : {C D : 2Cont} → 2ContHom C D
  → (F : 1Cont) (X : Set)
  → 2⟦ C ⟧ F X → 2⟦ D ⟧ F X
2⟦ record { f = f ; g₀ = g₀ ; g₁ = g₁ } ⟧Hom F X
  record { s = s ; k₀ = k₀ ; k₁ = k₁ } = record
  { s = f s
  ; k₀ = λ p → ⟦ F ⟧₁ (2⟦ g₀ s .ContHom.g p ⟧Hom F X) (k₀ (g₀ s .ContHom.f p))
  ; k₁ = k₁ ∘' g₁ s
  }
