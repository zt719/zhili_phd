{-# OPTIONS --cubical --guardedness --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma

record isWCat (Obj : Type) (Hom : Obj → Obj → Type) : Type where
  field
    id  : {A : Obj} → Hom A A
    _∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    idl : {A B : Obj} (f : Hom A B) → id ∘ f ≡ f
    idr : {A B : Obj} (f : Hom A B) → f ∘ id ≡ f
    ass : {A B C D : Obj} (h : Hom C D) (g : Hom B C) (f : Hom A B) →
           (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

_×Cat_ : ∀ {Obj₁ Hom₁ Obj₂ Hom₂} → isWCat Obj₁ Hom₁ → isWCat Obj₂ Hom₂
  → isWCat (Obj₁ × Obj₂) (λ{ (A , B) (A′ , B′) → Hom₁ A A′ × Hom₂ B B′ })
record { id = id ; _∘_ = _∘_ ; idl = idl ; idr = idr ; ass = ass } ×Cat record { id = id₁ ; _∘_ = _∘_₁ ; idl = idl₁ ; idr = idr₁ ; ass = ass₁ }
  = record { id = id , id₁ ; _∘_ = λ {A} {B} {C} z z₁ → (z .fst ∘ z₁ .fst) , (z .snd ∘ z₁ .snd ₁) ; idl = {!!} ; idr = {!!} ; ass = {!!} }

record Func {Obj₁ Obj₂ Hom₁ Hom₂}
  (ℂ : isWCat Obj₁ Hom₁) (𝔻 : isWCat Obj₂ Hom₂) : Type where
  open isWCat
  field
    F    : Obj₁ → Obj₂
    F₁   : ∀ {A B} → Hom₁ A B → Hom₂ (F A) (F B)
    F-id : ∀ {A} → F₁ (ℂ .id {A = A}) ≡ 𝔻 .id
    F-∘  : ∀ {A B C} (f : Hom₁ B C) (g : Hom₁ A B) → F₁ (ℂ ._∘_ f g) ≡ 𝔻 ._∘_ (F₁ f) (F₁ g)

NHom : ℕ → Type → Type
NHom zero Obj = ⊤
NHom (suc n) Obj = Σ[ Hom ∈ (Obj → Obj → Type) ] ((A B : Obj) → NHom n (Hom A B))

isNCat : (n : ℕ) → Σ[ Obj ∈ Type ] NHom n Obj → Type
isNCat zero (Obj , tt) = ⊤
isNCat (suc zero) (Obj , Hom , _) = isWCat Obj Hom × ((A B : Obj) → isSet (Hom A B))
isNCat (suc (suc n)) (Obj , Hom , Homⁿ)
  = isWCat Obj Hom
  × ((A B : Obj) → isNCat (suc n) (Hom A B , Homⁿ A B))
  × ((A B C : Obj) (HomCat : (A B : Obj) → isWCat (Hom A B) (Hom² A B))
    → Func (HomCat B C ×Cat HomCat A B) (HomCat A C))
  where
  Hom² : (A B : Obj) → Hom A B → Hom A B → Type
  Hom² A B = Homⁿ A B .fst
