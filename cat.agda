-- {-# OPTIONS --cubical #-}

module Cat where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
 
lone : Level
lone = lsuc lzero

open import Data.Nat
  using (ℕ; zero; suc)
open import Data.Product
  using (Σ-syntax; _×_; _,_)
open import Data.Empty
  using (⊥)
open import Data.Unit
  using (⊤; tt)
open import Data.Sum
  using (_⊎_)
open import Data.Bool
  using (Bool; true; false)
open import Data.Maybe
  using (Maybe; nothing; just)
  renaming (map to Maybe-map)
open import Data.List
  using (List; []; _∷_; head)
  renaming (map to List-map)
  
open import Function.Base
  using (id; flip; _∘′_)

open import Relation.Binary.PropositionalEquality
  renaming (trans to _∙_)
  
--open import Cubical.Foundations.Prelude using (Type; _≡_; refl; cong; cong₂; _∙_; funExt)

record Prop : Set₁ where
  field
    ⟦_⟧ : Set
    is-prop : {x y : ⟦_⟧} → x ≡ y
open Prop

⊤-prop : Prop
⟦ ⊤-prop ⟧ = ⊤
is-prop ⊤-prop = refl

⊥-prop : Prop
⟦ ⊥-prop ⟧ = ⊥
is-prop ⊥-prop = refl

_≤_ : ℕ → ℕ → Prop
zero ≤ m = ⊤-prop
suc n ≤ zero = ⊥-prop
suc n ≤ suc m = n ≤ m
  
≤-refl : {a : ℕ} → ⟦ a ≤ a ⟧
≤-refl {zero} = tt
≤-refl {suc a} = ≤-refl {a}

≤-trans : {a b c : ℕ} → ⟦ b ≤ c ⟧ → ⟦ a ≤ b ⟧ → ⟦ a ≤ c ⟧
≤-trans {zero} p q = tt
≤-trans {suc n} {suc m} {suc l} p q = ≤-trans {n} {m} {l} p q

record Preorder : Set₁ where
  constructor mkPreorder
  field
    X : Set
    R : X → X → Prop
    refll : {a : X} → ⟦ R a a ⟧
    transs : {a b c : X} → ⟦ R b c ⟧ → ⟦ R a b ⟧ → ⟦ R a c ⟧

ℕ-Preorder : Preorder
ℕ-Preorder = mkPreorder ℕ _≤_ (λ {a} → ≤-refl {a}) (λ {a} {b} {c} p q → ≤-trans {a} {b} {c} p q)

record Category {ℓ : _} : Set (lsuc ℓ) where
  constructor mkCategory
  infix  4 _≈_
  infixr 9 _∘_
  field
    ∣_∣ : Set ℓ
    Hom : ∣_∣ → ∣_∣ → Set
    _≈_ : {a b : ∣_∣} (f g : Hom a b) → Set
    Id  : (a : ∣_∣) → Hom a a
    _∘_ : {a b c : ∣_∣} → Hom b c → Hom a b → Hom a c
    idˡ : {a b : ∣_∣} {f : Hom a b} → Id b ∘ f ≈ f
    idʳ : {a b : ∣_∣} {f : Hom a b} → f ∘ Id a ≈ f
    assoc     : {a b c d : ∣_∣} {f : Hom c d} {g : Hom b c} {h : Hom a b}
              → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)

{-
_op : {ℓ : _} → Category {ℓ} → Category {ℓ}
mkCategory ∣_∣ Hom _≈_ Id _∘_ idˡ idʳ assoc op
  = mkCategory ∣_∣ (λ a b → Hom b a) _≈_ Id (λ f g → g ∘ f) idʳ idˡ (λ {a} {b} {c} {d} {f} {g} {h} → {!!})
-}

Preorder2Category : Preorder → Category
Preorder2Category (mkPreorder ∣_∣ R refll trans)
  = mkCategory ∣_∣ (λ a b → ⟦ R a b ⟧) _≡_ (λ _ → refll) trans (is-prop (R _ _)) (is-prop (R _ _)) (is-prop (R _ _))
  
record Monoid {ℓ : _} : Set (lsuc ℓ) where
  constructor mkMonoid
  field
    ∣_∣ : Set
    e : ∣_∣
    _∘_ : ∣_∣ → ∣_∣ → ∣_∣
    idˡ : {x : ∣_∣} → e ∘ x ≡ x
    idʳ : {x : ∣_∣} → x ∘ e ≡ x
    assoc : {x y z : ∣_∣} → (x ∘ y) ∘ z ≡ x ∘ (y ∘ z)

Monoid2Category : {ℓ : _} → Monoid {ℓ} → Category
Monoid2Category (mkMonoid ∣_∣ e _∘_ idˡ idʳ assoc)
  = mkCategory ⊤ (λ _ _ → ∣_∣) _≡_ (λ _ → e) _∘_ idˡ idʳ assoc
  
record Monoid-Hom {ℓ : _} (M₁ M₂ : Monoid {ℓ}) : Set where
  constructor mkMonoid-Hom
  open Monoid using (∣_∣; _∘_)
  open Monoid M₁ using () renaming (e to e₁; _∘_ to _∘₁_)
  open Monoid M₂ using () renaming (e to e₂; _∘_ to _∘₂_)
  field
    map : ∣ M₁ ∣ → ∣ M₂ ∣
    map-e : map e₁ ≡ e₂
    map-∘ : {a b : ∣ M₁ ∣} → map (a ∘₁ b) ≡ map a ∘₂ map b

Monoid-Hom-refl : {ℓ : _} (a : Monoid {ℓ}) → Monoid-Hom a a
Monoid-Hom-refl (mkMonoid ∣_∣ e _∘_ idˡ idʳ assoc)
  = mkMonoid-Hom id refl refl 

Monoid-Hom-trans : {ℓ : _} {a b c : Monoid {ℓ}} → Monoid-Hom b c → Monoid-Hom a b → Monoid-Hom a c
Monoid-Hom-trans (mkMonoid-Hom map map-e map-∘) (mkMonoid-Hom map₁ map-e₁ map-∘₁)
  = mkMonoid-Hom (map ∘′ map₁) (cong map map-e₁ ∙ map-e) (cong map map-∘₁ ∙ map-∘)

Eq-Monoid-Hom : {ℓ : _} {a b : Monoid {ℓ}} → Monoid-Hom a b → Monoid-Hom a b → Set
Eq-Monoid-Hom (mkMonoid-Hom map _ _) (mkMonoid-Hom map₁ _ _)
  = map ≡ map₁

Monoid-Category : {ℓ : _} → Category
Monoid-Category {ℓ}
  = mkCategory (Monoid {ℓ}) Monoid-Hom Eq-Monoid-Hom Monoid-Hom-refl Monoid-Hom-trans refl refl refl

SET : Category
SET
  = mkCategory Set (λ a b → a → b) _≡_ (λ _ → id) _∘′_ refl refl refl 

record Functor {ℓ₁ ℓ₂ : _} (C : Category {ℓ₁}) (D : Category {ℓ₂}): Set (ℓ₁ ⊔ ℓ₂) where
  constructor mkFunctor
  open Category using (∣_∣; Hom; Id)
  open Category C using () renaming (_∘_ to _∘c_)
  open Category D using (_≈_) renaming (_∘_ to _∘d_)
  field
    F₀ : ∣ C ∣ → ∣ D ∣
    F₁ : {a b : ∣ C ∣} → Hom C a b → Hom D (F₀ a) (F₀ b)
    Id≈ : {a : ∣ C ∣} →  F₁ (Id C a) ≈ Id D (F₀ a)
    comp≈ : {a b c : ∣ C ∣} {f : Hom C b c} {g : Hom C a b}
      → F₁ (f ∘c g) ≈ F₁ f ∘d F₁ g

_⇒_ = Functor



{-
List-Functor : SET ⇒ SET
List-Functor
  = mkFunctor List List-map List-Id≈ List-comp≈
  where
  List-Id≈ : {A : Set} → List-map (id {A = A}) ≡ id {A = List A}
  List-Id≈ i [] = []
  List-Id≈ i (x ∷ xs) = x ∷ List-Id≈ i xs

  List-comp≈ : {A C B : Set} {f : B → C} {g : A → B}
    → List-map (f ∘′ g) ≡ List-map f ∘′ List-map g
  List-comp≈ i [] = []
  List-comp≈ {f = f} {g} i (x ∷ xs) = f (g x) ∷ List-comp≈ {f = f} {g} i xs

Maybe-Functor : SET ⇒ SET
Maybe-Functor
  = mkFunctor Maybe Maybe-map Maybe-Id≈ Maybe-comp≈
  where
  Maybe-Id≈ : {A : Set} → Maybe-map (id {A = A}) ≡ id {A = Maybe A}
  Maybe-Id≈ i (just x) = just x
  Maybe-Id≈ i nothing = nothing

  Maybe-comp≈ : {A B C : Set} {f : B → C} {g : A → B}
    → Maybe-map (f ∘′ g) ≡ Maybe-map f ∘′ Maybe-map g
  Maybe-comp≈ {f = f} {g} i (just x) = just (f (g x))
  Maybe-comp≈ i nothing = nothing

U-Monoid→Set : {ℓ : _} → Monoid-Category {ℓ} ⇒ SET
U-Monoid→Set
  = mkFunctor Monoid.∣_∣ Monoid-Hom.map refl refl

record NaturalTransformation {ℓ₁ ℓ₂ : _} {C : Category {ℓ₁}} {D : Category {ℓ₂}}
  (F G : Functor C D) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor mkNT
  open Category using (∣_∣; Hom)
  open Category D using (_∘_; _≈_)
  open Functor F renaming (F₀ to F₀; F₁ to F₁)
  open Functor G renaming (F₀ to G₀; F₁ to G₁)  
  field
    α : (a : ∣ C ∣) → Hom D (F₀ a) (G₀ a)
    commute : {a b : ∣ C ∣} (f : Hom C a b)
      → α b ∘ F₁ f ≈ G₁ f ∘ α a

_~_ = NaturalTransformation

head-NT : List-Functor ~ Maybe-Functor
head-NT = mkNT (λ _ → head) commute
  where
  open Category SET
  commute : {A B : Set} (f : A → B) → head ∘ List-map f ≡ Maybe-map f ∘ head
  commute f i [] = nothing
  commute f i (x ∷ _) = just (f x)

record Algebra {ℓ₁ : _} {C : Category {ℓ₁}} (F : C ⇒ C) : Set ℓ₁ where
  open Category C
  open Functor F
  field
    c : ∣_∣
    f : Hom (F₀ c) c

-}
