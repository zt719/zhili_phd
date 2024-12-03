{-# OPTIONS --cubical #-}

{- tree types, with dom and appT -}

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude

{- Syntax -}

data Ty : Type where
  set : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

⟦_⟧T : Ty → Type₁
⟦ set ⟧T = Type
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

variable
  o o₁ o₂ h h₁ h₂ : Level

record Cat (Obj : Type o) {h} : Type (ℓ-suc (ℓ-max o h)) where
  field
    Hom : Obj → Obj → Type h
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} {f : Hom X Y} → id ∘ f ≡ f
    idr : ∀ {X Y} {f : Hom X Y} → f ∘ id ≡ f
    ass : ∀ {W X Y Z}{f : Hom X W}{g : Hom Y X}{h : Hom Z Y}
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

record Func
  {X : Type o₁} {Y : Type o₂}
  (C : Cat X {h₁}) (D : Cat Y {h₂})
  (F : X → Y) : Type (ℓ-max (ℓ-max o₁ h₁) (ℓ-max o₂ h₂)) where
  open Cat using (Hom)
  open Cat C using () renaming (_∘_ to _∘C_)
  open Cat D using () renaming (_∘_ to _∘D_)  
  field
    fmap : ∀ {X Y} → Hom C X Y → Hom D (F X) (F Y) 
    fmap∘ : ∀ {X Y Z}{f : Hom C Y Z}{g : Hom C X Y}
          → fmap (f ∘C g) ≡ (fmap f) ∘D (fmap g)

record Nat {X : Type o₁} {Y : Type o₂}(C : Cat X {h₁})(D : Cat Y {h₂})(F G : X → Y)
           (FF : Func C D F)(GG : Func C D G) : Type (ℓ-max (ℓ-max o₁ h₁) h₂) where
  open Cat using (Hom)           
  open Cat D renaming (_∘_ to _∘D_)
  open Func
  field
    α : (x : X) → Hom D (F x) (G x)
    nat : {x y : X}(f : Hom C x y) →
          fmap GG f ∘D α x ≡ α y ∘D fmap FF f


[_]o : (A : Ty) → Level
[_]h : (A : Ty) → Level
[_]f : (A : Ty) → Level

[ set ]o = ℓ-zero
[ A ⇒ B ]o = [ A ]o

[ set ]h = ℓ-zero
[ A ⇒ B ]h = ℓ-max (ℓ-suc ℓ-zero) [ B ]h

[ set ]f = ℓ-zero
[ A ⇒ B ]f = ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓ-zero) [ A ]h) [ B ]h) [ A ]f) [ B ]f

func : (A : Ty) → ⟦ A ⟧T → Type [ A ]f
cat : (A : Ty) → Cat ⟦ A ⟧T {[ A ]h}

func set _ = Unit
func (A ⇒ B) F =
  ((a : ⟦ A ⟧T) → func A a → func B (F a))
  × Func (cat A) (cat B) F

hom : (A : Ty) → ⟦ A ⟧T → ⟦ A ⟧T → Type [ A ]h
hom set X Y = X → Y
hom (A ⇒ B) f g = (a : ⟦ A ⟧T) → hom B (f a) (g a) 

cat set = record
  { Hom = λ X Y → X → Y
  ; id = λ X → X
  ; _∘_ = λ f g X → f (g X)
  ; idl = refl
  ; idr = refl
  ; ass = refl
  }
cat (A ⇒ B) = record
  { Hom = λ F G → (a : ⟦ A ⟧T) → Hom (F a) (G a) 
  ; id = λ F → id
  ; _∘_ = λ α β a → α a ∘B β a
  ; idl = λ {F} {G} {α} i a → idl {f = α a} i
  ; idr = λ {F} {G} {α} i a → idr {f = α a} i
  ; ass = λ {F} {G} {H} {J} {α} {β} {γ} i a → ass {f = α a} {g = β a} {h = γ a} i
  }
  where
    open Cat (cat B) renaming (_∘_ to _∘B_)  

{-


-- f : ℕ → ℕ
-- mono f = m ≤ n → f m ≤ f n

-- f g : ℕ → ℕ
-- f ≤ g = (n : ℕ) → f n ≤ g n

-- H : (ℕ → ℕ) → (ℕ → ℕ)
-- f ≤ g → H f ≤ H g
-- f mono → H f mono

data Ty : Type where
  nat : Ty
  _⇒_ : Ty → Ty → Ty

record Pre : (S : Type) (R : S → S → Type) where
  field
    rfl : ∀ {x : S} → R x x 
    trns : ∀ {x y z} → R x y → R y z → R x y

open Pre

mono : (A : Ty) → ⟦ A ⟧T → Type           ---→ func
order : (A : Ty) → ⟦ A ⟧T → ⟦ A ⟧T → Type ---→ hom
pre :  (A : Ty) → Pre ⟦ A ⟧T (order A)   ---→ cat 

mono nat _ = ⊤
mono (A ⇒ B) f =
  ((a : ⟦ A ⟧T) → mono A a → mono B (f a) )
  × ((a b : ⟦ A ⟧T) → order A a b → order B (f a) (f b))

order nat m n = m ≤ n
order (A ⇒ B) f g = (a : ⟦ A ⟧T) → order B (f a) (g a) 

pre nat = record { rfl = {!!} ; trns = {!!} }
pre (A ⇒ B) = record { rfl = λ a → rfl ; trns = λ xy yz a → trns (xy a) (yz a) }
  where open Pre (pre B)
-}
