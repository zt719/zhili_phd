-- {-# OPTIONS --cubical #-}

module Cat where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
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
import Function.Base

open import Relation.Binary.PropositionalEquality
  renaming (trans to _∙_)
  hiding ([_])
  
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

record Pre : Set₁ where
  constructor mkPre
  field
    X : Set
    R : X → X → Prop
    refll : {a : X} → ⟦ R a a ⟧
    transs : {a b c : X} → ⟦ R b c ⟧ → ⟦ R a b ⟧ → ⟦ R a c ⟧

ℕ-Pre : Pre
ℕ-Pre = mkPre ℕ _≤_ (λ {a} → ≤-refl {a}) (λ {a} {b} {c} p q → ≤-trans {a} {b} {c} p q)

record Cat {o ℓ e : _} : Set (lsuc (o ⊔ ℓ ⊔ e)) where
  constructor mkCat
  infix  4 _≈_
  infixr 9 _∘_
  infix  10 _[_,_] _[_≈_] _[_∘_]
  field
    Obj : Set o
    Hom : Obj → Obj → Set ℓ
    _≈_ : {a b : Obj} (f g : Hom a b) → Set e
    id  : {a : Obj} → Hom a a
    _∘_ : {a b c : Obj} → Hom b c → Hom a b → Hom a c
    id-l : {a b : Obj} {f : Hom a b} → id {b} ∘ f ≈ f
    id-r : {a b : Obj} {f : Hom a b} → f ∘ id {a} ≈ f
    assoc     : {a b c d : Obj} {f : Hom c d} {g : Hom b c} {h : Hom a b}
              → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)

  ∣_∣ = Obj
  _[_,_] = Hom
  _[_≈_] = _≈_
  _[_∘_] = _∘_

Pre2Cat : Pre → Cat
Pre2Cat (mkPre Obj R refll trans)
  = mkCat Obj (λ a b → ⟦ R a b ⟧) _≡_ refll trans (is-prop (R _ _)) (is-prop (R _ _)) (is-prop (R _ _))

record Mon {o e : _} : Set (lsuc (o ⊔ e)) where
  constructor mkMon
  infix  4 _≈_
  infixr 9 _∘_
  infix  10 _[_≈_] _[_∘_]  
  field
    Obj : Set o
    _≈_ : (a b : Obj) → Set e    
    a : Obj
    _∘_ : Obj → Obj → Obj
    id-l : {x : Obj} → a ∘ x ≈ x
    id-r : {x : Obj} → x ∘ a ≈ x
    assoc : {x y z : Obj} → (x ∘ y) ∘ z ≈ x ∘ (y ∘ z)

  ∣_∣ = Obj
  _[_≈_] = _≈_
  _[_∘_] = _∘_
  _∙ = a

Mon2Cat : {o ℓ e : _} → Mon {o} {e} → Cat {lzero} {o} {e}
Mon2Cat (mkMon Obj _≈_ a _∘_ id-l id-r assoc)
  = mkCat ⊤ (λ _ _ → Obj) _≈_ a _∘_ id-l id-r assoc

record Mon-Hom {o e : _} (M N : Mon {o} {e}) : Set (e ⊔ o) where
  constructor mkMon-Hom
  open Mon
  field
    f : ∣ M ∣ → ∣ N ∣
    f-∙ : N [ f (M ∙) ≈ N ∙ ]
    f-∘ : {a b : ∣ M ∣} → N [ f (M [ a ∘ b ]) ≈ N [ f a ∘ f b ] ]

{-
postulate
  MON : {o ℓ e : _} → Cat {o} {ℓ} {e}
-}

SET : {o : _} → Cat {lsuc o} {o} {o}
Cat.Obj (SET {o}) = Set o
Cat.Hom SET a b = a → b
Cat._≈_ SET = _≡_
Cat.id SET = Function.Base.id
Cat._∘_ SET = Function.Base._∘′_
Cat.id-l SET = refl
Cat.id-r SET = refl
Cat.assoc SET = refl

SET₀ = SET {lzero}

record Func {o ℓ e o′ ℓ′ e′ : _} (C : Cat {o} {ℓ} {e}) (D : Cat {o′} {ℓ′} {e′}) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  constructor mkFunc
  open Cat
  field
    F₀ : ∣ C ∣ → ∣ D ∣
    F₁ : {a b : ∣ C ∣} → C [ a , b ] → D [ F₀ a , F₀ b ]
    id≈ : {a : ∣ C ∣} → D [ F₁ {a} (id C) ≈ id D ]
    comp≈ : {a b c : ∣ C ∣} {f : C [ b , c ]} {g : C [ a , b ]}
      → D [ F₁ (C [ f ∘ g ]) ≈ D [ F₁ f ∘ F₁ g ] ]

  _₀ = F₀
  _₁ = F₁

{-
List-Func : Func SET SET
List-Func
  = mkFunc List List-map List-Id≈ List-comp≈
  where
  List-Id≈ : {A : Set} → List-map (id {A = A}) ≡ id {A = List A}
  List-Id≈ i [] = []
  List-Id≈ i (x ∷ xs) = x ∷ List-Id≈ i xs

  List-comp≈ : {A C B : Set} {f : B → C} {g : A → B}
    → List-map (f ∘′ g) ≡ List-map f ∘′ List-map g
  List-comp≈ i [] = []
  List-comp≈ {f = f} {g} i (x ∷ xs) = f (g x) ∷ List-comp≈ {f = f} {g} i xs

Maybe-Func : Func SET SET
Maybe-Func
  = mkFunc Maybe Maybe-map Maybe-Id≈ Maybe-comp≈
  where
  Maybe-Id≈ : {A : Set} → Maybe-map (id {A = A}) ≡ id {A = Maybe A}
  Maybe-Id≈ i (just x) = just x
  Maybe-Id≈ i nothing = nothing

  Maybe-comp≈ : {A B C : Set} {f : B → C} {g : A → B}
    → Maybe-map (f ∘′ g) ≡ Maybe-map f ∘′ Maybe-map g
  Maybe-comp≈ {f = f} {g} i (just x) = just (f (g x))
  Maybe-comp≈ i nothing = nothing
-}


{-
U-Mon→Set : {ℓ : _} → Func (Mon-Cat {ℓ}) SET
U-Mon→Set
  = mkFunc Mon.Obj Mon-Hom.map refl refl
-}

record NT {o ℓ e o′ ℓ′ e′ : _} {C : Cat {o} {ℓ} {e}} {D : Cat {o′} {ℓ′} {e′}}
  (F G : Func C D) : Set (o ⊔ ℓ ⊔ e ⊔ e′ ⊔ ℓ′ ⊔ e′) where
  constructor mkNT
  open Cat
  open Func
  field
    α : (a : ∣ C ∣) → D [ (F ₀) a , (G ₀) a ]
    commute : {a b : ∣ C ∣} (f : C [ a , b ])
      → D [ D [ α b ∘ (F ₁) f ] ≈ D [ (G ₁) f ∘ α a ] ]

{-
head-NT : NT List-Func Maybe-Func
head-NT = mkNT (λ _ → head) commute
  where
  open Cat SET
  commute : {A B : Set} (f : A → B) → head ∘ List-map f ≡ Maybe-map f ∘ head
  commute f i [] = nothing
  commute f i (x ∷ _) = just (f x)
-}

{-
record Alg {ℓ₁ : _} {C : Cat {ℓ₁}} (F : Func C C) : Set ℓ₁ where
  open Cat C
  open Func F
  field
    c : Obj
    f : Hom (F₀ c) c
-}

postulate
  NT-refl : {a : Func SET₀ SET₀} → NT a a

  NT-trans : {a b c : Func SET₀ SET₀} → NT b c → NT a b → NT a c
  NT-id-r : {a b : Func SET₀ SET₀} {f : NT a b} → NT-trans NT-refl f ≡ f
  NT-id-l : {a b : Func SET₀ SET₀} {f : NT a b} → NT-trans f NT-refl ≡ f
  NT-assoc : {a b c d : Func SET₀ SET₀} {f : NT c d} {g : NT b c} {h : NT a b}
    → NT-trans (NT-trans f g) h ≡ NT-trans f (NT-trans g h)


SET₀⇒SET₀ : Cat {lsuc lzero} {lsuc lzero} {lsuc lzero}
SET₀⇒SET₀ = mkCat (Func SET₀ SET₀) NT _≡_ NT-refl NT-trans NT-id-r NT-id-l NT-assoc



