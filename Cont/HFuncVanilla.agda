module HFuncVanilla where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Sum
open import Data.Product

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

variable  A B C : Ty

⟦_⟧t : Ty → Set₁
⟦ * ⟧t = Set
⟦ A ⇒ B ⟧t = ⟦ A ⟧t → ⟦ B ⟧t

record Cat (Obj : Set₁) : Set₂ where
  infixr 9 _∘_
  field
    Hom : Obj → Obj → Set₁
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z

record Func {A B : Set₁} (ℂ : Cat A) (𝔻 : Cat B) (F : A → B) : Set₁ where
  open Cat
  field
    F₁ : ∀ {X Y} → Hom ℂ X Y → Hom 𝔻 (F X) (F Y)

record Nat {A B : Set₁} (ℂ : Cat A) (𝔻 : Cat B)
  (F G : A → B) (FF : Func ℂ 𝔻 F) (GG : Func ℂ 𝔻 G) : Set₁ where
  open Cat
  open Func
  field
    η : ∀ X → Hom 𝔻 (F X) (G X)

⟦_⟧HFunc : (A : Ty) → ⟦ A ⟧t → Set₁

⟦_⟧HCat : (A : Ty) → Cat (Σ ⟦ A ⟧t ⟦ A ⟧HFunc)

⟦ * ⟧HFunc X = Lift (lsuc lzero) ⊤
⟦ A ⇒ B ⟧HFunc H =
  Σ[ HH ∈ ({F : ⟦ A ⟧t} → ⟦ A ⟧HFunc F → ⟦ B ⟧HFunc (H F)) ]
  Func ⟦ A ⟧HCat ⟦ B ⟧HCat (λ (F , FF) → H F , HH {F} FF)

⟦ * ⟧HCat = record
  { Hom = λ (X , lift tt) (Y , lift tt) → Lift (lsuc lzero) (X → Y)
  ; id = lift (λ x → x)
  ; _∘_ = λ{ (lift f) (lift g) → lift (λ x → f (g x)) }
  }
  
⟦ A ⇒ B ⟧HCat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧HCat ⟦ B ⟧HCat
    (λ (X , XX) → F X , FF {X} XX)
    (λ (X , XX) → G X , GG {X} XX)
    FFF GGG
  ; id = record { η = λ X → id }
  ; _∘_ = λ α β → record { η = λ X → α .η X ∘ β .η X }
  }
  where
    open Cat ⟦ B ⟧HCat
    open Nat
