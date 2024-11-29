{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
  hiding (J)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
  hiding (_⇒_)

variable
  o₁ o₂ h₁ h₂ : Level

data Ty : Type where
  set : Ty
  _⇒_ : Ty → Ty → Ty

record Set′ : Type₁ where
  field
    ∣_∣ : Type
    is-set : isSet ∣_∣
open Set′

open Category

IdLTrans
  : {C : Category o₁ h₁} {D : Category o₂ h₂} {F G : Functor C D}
  → (α : NatTrans F G) → idTrans F ●ᵛ α ≡ α
IdLTrans {D = D} α = makeNatTransPath (funExt (λ X → ⋆IdL D _))

IdRTrans
  : {C : Category o₁ h₁} {D : Category o₂ h₂} {F G : Functor C D}
  → (α : NatTrans F G) → α ●ᵛ idTrans G ≡ α
IdRTrans {D = D} α = makeNatTransPath (funExt (λ X → ⋆IdR D _))

AssocTrans
  : {C : Category o₁ h₁} {D : Category o₂ h₂} {F G H J : Functor C D}
  → (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H J)
  → (α  ●ᵛ β)  ●ᵛ γ ≡ α ●ᵛ (β  ●ᵛ γ) 
AssocTrans {D = D} α β γ = makeNatTransPath (funExt (λ X → ⋆Assoc D _ _ _))

[_]o : Ty → Level
[_]h : Ty → Level
[_]c : (A : Ty) → Category [ A ]o [ A ]h

[ set ]o = ℓ-suc ℓ-zero
[ A ⇒ B ]o = [ A ]o ⊔ [ A ]h ⊔ [ B ]o ⊔ [ B ]h

[ set ]h = ℓ-zero
[ A ⇒ B ]h = [ A ]o ⊔ [ A ]h ⊔ [ B ]h

[ set ]c =
  record
   { ob = Set′
   ; Hom[_,_] = λ X Y → ∣ X ∣ → ∣ Y ∣
   ; id = λ X → X
   ; _⋆_ = λ f g X → g (f X)
   ; ⋆IdL = λ f → refl
   ; ⋆IdR = λ f → refl
   ; ⋆Assoc = λ f g h → refl
   ; isSetHom = λ {X} {Y} f g p q i j x →
     is-set Y (f x) (g x) (funExt⁻ p x) (funExt⁻ q x) i j
   }

[ A ⇒ B ]c =
  record
   { ob = Functor [ A ]c [ B ]c
   ; Hom[_,_] = NatTrans
   ; id = idTrans _
   ; _⋆_ = λ α β → compTrans β α
   ; ⋆IdL = IdLTrans
   ; ⋆IdR = IdRTrans
   ; ⋆Assoc = AssocTrans
   ; isSetHom = isSetNatTrans
   }
