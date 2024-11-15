{-# OPTIONS --guardedness #-}

module HFunc where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
  hiding ([_])
open import Function.Base

infixr 5 _⇒_
data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

infixl 5 _▷_
data Con : Set where
  • : Con
  _▷_ : Con → Ty → Con

-- dom (A ⇒ B ⇒ set) = • ▷ B ▷ A
dom : Ty → Con
dom set = •
dom (A ⇒ B) = dom B ▷ A

variable A B C : Ty
variable Γ Δ : Con

⟦_⟧T : Ty → Set₁
⟦ set ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

data Unit : Set₁ where
  * : Unit

⟦_⟧C : Con → Set₁
⟦ • ⟧C = Unit
⟦ Γ ▷ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

TT = (set ⇒ set) ⇒ set ⇒ set

{-
record Func : Set₁ where
  field
    T₀ : Set → Set
    T₁ : {X Y : Set} → (X → Y) → T₀ X → T₀ Y
    T-id : {X : Set} → T₁ {X} id ≡ id
    T-∘ : {X Y Z : Set} {f : Y → Z} {g : X → Y}
      → T₁ (f ∘ g) ≡ T₁ f ∘ T₁ g

record Func₁ : Set₁ where
  field
    T₀ : (Set → Set) × Set → Set
    T₁ : {F G : Set → Set} → ({X : Set} → F X → G X)
      → {X : Set} → T₀ (F , X) → T₀ (G , X)
    T-id : {F : Set → Set} {X : Set} → T₁ {F} id {X} ≡ id
    T-∘ : {F G H : Set → Set} {α : {X : Set} → G X → H X}
      → {β : {X : Set} → F X → G X}
      → {X : Set} → T₁ (α {X} ∘ β) {X} ≡ T₁ α ∘ T₁ β

record Func₂ : Set₁ where
  field
    T₀ : (Set × Set → Set) × (Set → Set) → Set
    T₁ : {F G : Set × Set → Set} → ({X : Set × Set} → F X → G X)
      → {X : Set → Set} → T₀ (F , X) → T₀ (G , X)
    T-id : {F : Set × Set → Set} {X : Set → Set} → T₁ {F} id {X} ≡ id

record Func₃ : Set₁ where
  field
    T₀ : (Set × (Set → Set) → Set) × (Set → Set) × Set → Set
    T₁ : {F G : Set × (Set → Set) → Set} 
      → ({X : Set × (Set → Set)} → F X → G X)
      → {X : (Set → Set) × Set} → T₀ (F , X) → T₀ (G , X)
    T-id : {F : Set × (Set → Set) → Set} {X : (Set → Set) × Set} → T₁ {F} id {X} ≡ id
-}

record HFunc (A B : Ty) : Set₁ where
  field
    T₀ : (⟦ dom A ⟧C → Set) → ⟦ dom B ⟧C → Set
    T₁ : {F G : ⟦ dom A ⟧C → Set} → ({X : ⟦ dom A ⟧C} → F X → G X)
      → {X : ⟦ dom B ⟧C} → T₀ F X → T₀ G X
    T-id : {F : ⟦ dom A ⟧C → Set} {X : ⟦ dom B ⟧C } → T₁ {F} id {X} ≡ id
    T-∘  : {F G H : ⟦ dom A ⟧C → Set} {α : {X : ⟦ dom A ⟧C} → G X → H X}
      {β : {X : ⟦ dom A ⟧C} → F X → G X} {X : ⟦ dom B ⟧C} → T₁ {F} (α ∘ β) {X} ≡ T₁ α ∘ T₁ β
open HFunc      

postulate
  funExt : {A : Set} {P : A → Set} {f g : (x : A) → P x} → ((x : A) → f x ≡ g x) → f ≡ g

Maybe-Func : HFunc set set
T₀ Maybe-Func x * = Maybe (x *)
T₁ Maybe-Func f {*} (just x) = just (f x)
T₁ Maybe-Func f {*} nothing = nothing
T-id Maybe-Func {X = *} = funExt λ{ (just x) → refl ; nothing → refl }
T-∘ Maybe-Func {X = *} = funExt λ{ (just x) → refl ; nothing → refl }

L : (Set → Set) → Set → Set
L F X = ⊤ ⊎ X × F X

L-Func : HFunc (set ⇒ set) (set ⇒ set)
T₀ L-Func F X = L (curry F *) (proj₂ X)
T₁ L-Func f (inj₁ tt) = inj₁ tt
T₁ L-Func f (inj₂ (x , xs)) = inj₂ (x , f xs)
T-id L-Func = funExt λ{ (inj₁ tt) → refl ; (inj₂ (x , xs)) → refl }
T-∘ L-Func = funExt λ{ (inj₁ tt) → refl ; (inj₂ (x , xs)) → refl }

{-
H : (Set → Set) → Set → Set
H F X = X × F (F X)

H-Func : HFunc (set ⇒ set) (set ⇒ set)
HFunc.T₀ H-Func x y = H (curry x *) (proj₂ y)
proj₁ (HFunc.T₁ H-Func α (x , ffx)) = x 
proj₂ (HFunc.T₁ H-Func α (x , ffx)) = HFunc.T₁ {!!} {!!} {!!}
HFunc.T-id H-Func = {!!}
HFunc.T-∘ H-Func = {!!}
-}
