{-# OPTIONS --type-in-type --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

{- Syntax -}

data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

⟦_⟧T : Ty → Set
⟦ set ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

record Cat (Obj : Set) : Set where
  field
    Hom : Obj → Obj → Set
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} {f : Hom X Y} → id ∘ f ≡ f
    idr : ∀ {X Y} {f : Hom X Y} → f ∘ id ≡ f
    ass : ∀ {W X Y Z} {f : Hom X W} {g : Hom Y X} {h : Hom Z Y}
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

record Func {X Y : Set}(C : Cat X)(D : Cat Y)(F : X → Y) : Set where
  open Cat
  open Cat C renaming (_∘_ to _∘C_)
  open Cat D renaming (_∘_ to _∘D_)  
  field
    fmap : ∀ {X Y} → Hom C X Y → Hom D (F X) (F Y)
    fmapid : ∀ {X} → fmap {X} (id C) ≡ id D
    fmap∘ : ∀ {X Y Z} (f : Hom C Y Z) (g : Hom C X Y)
          → fmap (f ∘C g) ≡ (fmap f) ∘D (fmap g)

record Nat {X Y : Set}(C : Cat X)(D : Cat Y)(F G : X → Y)
           (FF : Func C D F)(GG : Func C D G) : Set where
  open Cat
  open Cat D renaming (_∘_ to _∘D_)
  open Func
  field
    η : ∀ X → Hom D (F X) (G X)
    nat : ∀ {X Y} (f : Hom C X Y) →
          fmap GG f ∘D η X ≡ η Y ∘D fmap FF f

⟦_⟧F : (A : Ty) → ⟦ A ⟧T → Set
⟦_⟧C : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧F)

⟦ set ⟧F X = Unit
⟦ A ⇒ B ⟧F F = Σ[ FF ∈ ((X : ⟦ A ⟧T) → ⟦ A ⟧F X → ⟦ B ⟧F (F X)) ]
               Func ⟦ A ⟧C ⟦ B ⟧C (λ (X , XX) → F X , FF X XX)

⟦ set ⟧C = record
  { Hom = λ (X , _) (Y , _) → X → Y
  ; id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; idl = refl
  ; idr = refl
  ; ass = refl
  }

⟦ A ⇒ B ⟧C = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧C ⟦ B ⟧C (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG
  ; id = record { η = λ x → id ; nat = λ f → idr ∙ sym idl }
  ; _∘_ = λ{ record { η = η ; nat = nat } record { η = β ; nat = nat₁ }
    → record { η = λ x → η x ∘ β x ; nat = λ f → sym ass ∙ cong (_∘ _) (nat f)
              ∙ ass ∙ cong (_ ∘_) (nat₁ f) ∙ sym ass } }
  ; idl = _
  ; idr = _
  ; ass = _
  }
  where
    open Cat ⟦ B ⟧C

TN : ⟦ set ⇒ set ⟧T
TN X = Unit ⊎ X

FN : ⟦ set ⇒ set ⟧F TN
FN = _ , record
  { fmap = λ{ f (inl tt) → inl tt ; f (inr x) → inr (f x) }
  ; fmapid = λ{ i (inl tt) → inl tt ; i (inr x) → inr x }
  ; fmap∘ = λ{ f g i (inl tt) → inl tt ; f g i (inr x) → inr (f (g x)) }
  }

B : ⟦ (set ⇒ set) ⇒ (set ⇒ set) ⟧T
B F X = X × F (F X)

BF : ⟦ (set ⇒ set) ⇒ (set ⇒ set) ⟧F B
BF = (λ X x → {!!} , {!!}) , record { fmap = {!!} ; fmapid = {!!} ; fmap∘ = {!!} }
