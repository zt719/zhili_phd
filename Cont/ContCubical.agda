{-# OPTIONS --cubical --guardedness #-}

module ContCubical where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Instances.Sets

open import Cubical.Data.Empty
open import Cubical.Data.Unit
  renaming (Unit to ⊤; isSetUnit to isSet⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

{- Container -}
record Cont : Type₁ where
  constructor _◃_&_&_
  field
    S : Type
    P : S → Type
    isSetS : isSet S
    isSetP : (s : S) → isSet (P s)

variable SP TQ : Cont

record ContHom (SP TQ : Cont) : Type where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q; isSetS to isSetT; isSetP to isSetQ)
  field
    f : S → T
    g : (s : S) → Q (f s) → P s

⟦_⟧ : Cont → Functor (SET ℓ-zero) (SET ℓ-zero)
⟦ S ◃ P & isSetS & isSetP ⟧
  = record
  { F-ob = λ (X , isSetX) → (Σ[ s ∈ S ] (P s → X)) , (isSetΣ isSetS (λ s → isSet→ isSetX))
  ; F-hom = λ f (s , k) → s , λ p → f (k p)
  ; F-id = λ i (s , k) → s , k
  ; F-seq = λ f g i (s , k) → s , λ p → g (f (k p))
  }

⟦_⟧Hom : ContHom SP TQ → NatTrans (⟦ SP ⟧) (⟦ TQ ⟧)
⟦_⟧Hom (f ◃ g) = natTrans
  (λ X (s , k) → f s , λ p → k (g s p))
  (λ α i (s , k) → f s , λ p → α (k (g s p)))

open Category
open ContHom

CONT : Category (ℓ-suc ℓ-zero) ℓ-zero
CONT .ob = Cont 
CONT .Hom[_,_] = ContHom
CONT .id = (λ s → s) ◃ (λ s p → p)
CONT ._⋆_ (f ◃ g) (f′ ◃ g′) = (λ s → f′ (f s)) ◃ (λ s p → g s (g′ (f s) p))
CONT .⋆IdL (f ◃ g) i = f ◃ g
CONT .⋆IdR (f ◃ g) i = f ◃ g
CONT .⋆Assoc (f ◃ g) (f′ ◃ g′) (f′′ ◃ g′′) i
  = (λ s → f′′ (f′ (f s))) ◃ (λ s p → g s (g′ (f s) (g′′ (f′ (f s)) p)))
f (CONT .isSetHom {S ◃ P & isSetS & isSetP} {T ◃ Q & isSetT & isSetQ} m n p q i j) s =
  isSetT (f m s) (f n s) (λ k → f (p k) s) (λ k → f (q k) s) i j
g (CONT .isSetHom {S ◃ P & isSetS & isSetP} {T ◃ Q & isSetT & isSetQ} m n p q i j) s = 
  isSet→SquareP
    {A = λ i j → Q (isSetT (f m s) (f n s) (λ k → f (p k) s) (λ k → f (q k) s) i j) → P s}
     (λ _ _ → isSet→ (isSetP s))
     (λ k → g (p k) s)
     (λ k → g (q k) s)
     (λ _ → g m s)
     (λ _ → g n s)
     i j

one : Cont
one = ⊤ ◃ (λ s → ⊥) & isSet⊤ & (λ s → λ ())

_×C_ : Cont → Cont → Cont
(S ◃ P & isSetS & isSetP) ×C (T ◃ Q & isSetT & isSetQ)
  = (S × T) ◃ (λ (s , t) → P s ⊎ Q t)
  & isSet× isSetS isSetT & (λ (s , t) → isSet⊎ (isSetP s) (isSetQ t))

zero : Cont
zero = ⊥ ◃ (λ ()) & (λ ()) & (λ ())

_⊎C_ : Cont → Cont → Cont
(S ◃ P & isSetS & isSetP) ⊎C (T ◃ Q & isSetT & isSetQ)
  = (S ⊎ T) ◃ (λ{ (inl s) → P s ; (inr t) → Q t })
  & isSet⊎ isSetS isSetT & (λ{ (inl s) → isSetP s ; (inr t) → isSetQ t })

{-
zero-𝟘 : Initial CONT
zero-𝟘 = zero , λ (S ◃ P & isSetS & isSetP) → ((λ ()) ◃ (λ ())) , λ (f ◃ g) i → {!!}

one-𝟙 : Terminal CONT
one-𝟙 = one , λ y → ((λ s → tt) ◃ (λ s → λ ())) , λ (f ◃ g) i → {!!}
-}

⊥-𝟘 : Initial (SET ℓ-zero)
⊥-𝟘 = (⊥ , λ ()) , λ y → (λ ()) , λ{ g i () }

⊤-𝟙 : Terminal (SET ℓ-zero)
⊤-𝟙 = (⊤ , isSet⊤) , λ y → (λ _ → tt) , λ g i x → tt
