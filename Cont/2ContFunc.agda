{-# OPTIONS --guardedness --type-in-type #-}

module Cont.2ContFunc where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding (J)

variable X Y : Set

postulate
  funExt :
    ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
    {f g : (a : A) → B a} →
    ((a : A) → f a ≡ g a) →
    f ≡ g

{- Containers -}

infix  0 _◃_
infixr 0 _→ᶜ_

record Cont : Set where
  constructor _◃_
  field
    S : Set
    P : S → Set
    
variable
  SP TQ SP' TQ' UV UV' F G : Cont

⟦_⟧ : Cont → Set → Set
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : (SP : Cont) → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g (s , f) = s , g ∘ f

{- Category of Containers -}

record _→ᶜ_ (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    fS : S → T
    fP : (s : S) → Q (fS s) → P s

record 2Cont : Set where
  inductive
  pattern
  constructor _◃_+_+_
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

variable H J SPPR TQQL : 2Cont

2⟦_⟧S' : (H : 2Cont) (T : Set) (Q : T → Set) → Set
2⟦ S ◃ PX + PF + RF ⟧S' T Q
  = Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ T ] (Q t → 2⟦ RF s pf ⟧S' T Q))

2⟦_⟧P' : (H : 2Cont) (T : Set) (Q : T → Set) → 2⟦ H ⟧S' T Q → Set
2⟦ S ◃ PX + PF + RF ⟧P' T Q (s , f)
  = Σ[ pf ∈ PF s ] let (t , f') = f pf in
    Σ[ q ∈ Q t ] (2⟦ RF s pf ⟧P' T Q (f' q) ⊎ PX s)

2⟦_⟧S : (H : 2Cont) (TQ : Cont) → Set
2⟦ H ⟧S (T ◃ Q) = 2⟦ H ⟧S' T Q

2⟦_⟧P : (H : 2Cont) (TQ : Cont) → 2⟦ H ⟧S TQ → Set
2⟦ H ⟧P (T ◃ Q) = 2⟦ H ⟧P' T Q

2⟦_⟧ : 2Cont → Cont → Cont
2⟦ H ⟧ F = 2⟦ H ⟧S F ◃ 2⟦ H ⟧P F

record Cat (Obj : Set) : Set where
  infixr 9 _o_
  field
    Hom : Obj → Obj → Set
    Id : ∀ {X} → Hom X X
    _o_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z

record Func {A B : Set} (ℂ : Cat A) (𝔻 : Cat B) (F : A → B) : Set where
  open Cat
  field
    F₁ : ∀ {X Y} → Hom ℂ X Y → Hom 𝔻 (F X) (F Y)

record Nat {A B : Set} (ℂ : Cat A) (𝔻 : Cat B)
  (F G : A → B) (FF : Func ℂ 𝔻 F) (GG : Func ℂ 𝔻 G) : Set where
  open Cat
  open Func
  field
    η : ∀ X → Hom 𝔻 (F X) (G X)

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

⟦_⟧T : Ty → Set
⟦ * ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧Func : (A : Ty) → ⟦ A ⟧T → Set

HFunc : (A : Ty) → Set₁
HFunc A = Σ ⟦ A ⟧T ⟦ A ⟧Func

⟦_⟧Cat : (A : Ty) → Cat (HFunc A)

⟦ * ⟧Func X = ⊤
⟦ A ⇒ B ⟧Func H =
  Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧Func F → ⟦ B ⟧Func (H F)) ]
  Func ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (F , FF) → H F , HH F FF)

⟦ * ⟧Cat = record
  { Hom = λ (X , tt) (Y , tt) → X → Y
  ; Id = λ x → x
  ; _o_ = λ f g x → f (g x)
  }
⟦ A ⇒ B ⟧Cat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG) → Nat ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG
  ; Id = record { η = λ X → ⟦ B ⟧Cat .Cat.Id }
  ; _o_ = λ α β → record { η = λ X → ⟦ B ⟧Cat .Cat._o_ (α .Nat.η X) (β .Nat.η X) }
  }

Set→ : Set → HFunc *
Set→ X = X , tt

Cont→ : Cont → HFunc (* ⇒ *)
Cont→ SP = ⟦ SP ⟧ , (λ _ _ → tt) , record { F₁ = ⟦ SP ⟧₁ }
