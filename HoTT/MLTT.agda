{-# OPTIONS --guardedness #-}

open import Data.Product hiding (curry; uncurry)
open import Relation.Binary.PropositionalEquality

variable
  A : Set
  B : A → Set
  C : (a : A) → B a → Set
  D : (a : A) (b : B a) → C a b → Set

Π : (A : Set) → (A → Set) → Set
Π A B = (a : A) → B a

curry : ((ab : Σ[ a ∈ A ] B a) → C (ab .proj₁) (ab .proj₂))
  → (a : A) (b : B a) → C a b
curry f a b = f (a , b)

uncurry : ((a : A) (b : B a) → C a b)
  → ((ab : Σ[ a ∈ A ] B a) → C (ab .proj₁) (ab .proj₂))
uncurry f (a , b) = f a b

assoc : Σ[ (a , b) ∈ Σ[ a ∈ A ] B a ] C a b
  → Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b
assoc ((a , b) , c) = (a , (b , c))

unassoc : Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b
  → Σ[ (a , b) ∈ Σ[ a ∈ A ] B a ] C a b
unassoc (a , (b , c)) = ((a , b) , c)

choice : ((a : A) → Σ[ b ∈ B a ] C a b)
  → Σ[ f ∈ ((a : A) → B a) ] ((a : A) → C a (f a))
choice g = (λ a → g a .proj₁) , (λ a → g a .proj₂)

choice₂ : ((a : A) (b : B a) → Σ[ c ∈ C a b ] D a b c)
  → Σ[ f ∈ ((a : A) (b : B a) → C a b) ] ((a : A) (b : B a) → D a b (f a b))
choice₂ g = (λ a b → g a b .proj₁) , (λ a b → g a b .proj₂)

pathlift : {A : Set} (P : A → Set)
  {x : A} (u : P x) {y : A} (p : x ≡ y) → (x , u) ≡ (y , subst P p u)
pathlift P u refl = refl

apd : {A : Set} {P : A → Set}
  (f : (x : A) → P x)
  {x y : A} (p : x ≡ y)
  → subst P p (f x) ≡ f y
apd f refl = refl

