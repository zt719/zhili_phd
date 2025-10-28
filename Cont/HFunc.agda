{-# OPTIONS --cubical --guardedness #-}

module Cont.HFunc where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

record Cat (Obj : Type₁) : Type₂ where
  infixr 9 _∘_
  field
    Hom : Obj → Obj → Type₁
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    ass : ∀ {W X Y Z} (f : Hom X W) (g : Hom Y X) (h : Hom Z Y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

record Func {A B : Type₁} (ℂ : Cat A) (𝔻 : Cat B) (F : A → B) : Type₁ where
  open Cat
  field
    F₁ : ∀ {X Y} → Hom ℂ X Y → Hom 𝔻 (F X) (F Y)
    F-id : ∀ {X} → F₁ {X} (ℂ .id) ≡ 𝔻 .id
    F-∘ : ∀ {X Y Z} (f : Hom ℂ Y Z) (g : Hom ℂ X Y)
          → F₁ (ℂ ._∘_ f g ) ≡ 𝔻 ._∘_ (F₁ f) (F₁ g)

record Nat {A B : Type₁} (ℂ : Cat A) (𝔻 : Cat B)
  (F G : A → B) (FF : Func ℂ 𝔻 F) (GG : Func ℂ 𝔻 G) : Type₁ where
  open Cat
  open Func
  field
    η : ∀ X → Hom 𝔻 (F X) (G X)
    nat : ∀ {X Y} (f : Hom ℂ X Y)
      → 𝔻 ._∘_ (GG .F₁ f) (η X) ≡ 𝔻 ._∘_ (η Y) (FF .F₁ f)

postulate
  Nat≡ : {A B : Type₁} {ℂ : Cat A} {𝔻 : Cat B} {F G : A → B}
    → {FF : Func ℂ 𝔻 F} {GG : Func ℂ 𝔻 G}
    → {α β : Nat ℂ 𝔻 F G FF GG}
    → α .Nat.η ≡ β .Nat.η → α ≡ β

{- Syntax -}

infixr 20 _⇒_
data Ty : Type where
  * : Ty
  _⇒_ : Ty → Ty → Ty
  
{- Semantics -}

⟦_⟧T : Ty → Type₁
⟦ * ⟧T = Type
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧Func : (A : Ty) → ⟦ A ⟧T → Type₁

⟦_⟧Cat : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧Func)

⟦ * ⟧Func X = Lift ⊤
⟦ A ⇒ B ⟧Func H =
  Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧Func F → ⟦ B ⟧Func (H F)) ]
  Func ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (F , FF) → H F , HH F FF)

⟦ * ⟧Cat = record
  { Hom = λ (X , lift tt) (Y , lift tt) → Lift (X → Y)
  ; id = lift (λ x → x)
  ; _∘_ = λ{ (lift f) (lift g) → lift (λ x → f (g x)) }
  ; idl = λ f → refl
  ; idr = λ f → refl
  ; ass = λ f g h → refl
  }
⟦ A ⇒ B ⟧Cat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG
  ; id = record
    { η = λ X → id
    ; nat = λ f → idr _ ∙ sym (idl _)
    }
  ; _∘_ = λ α β → record
    { η = λ X → α .η X ∘ β .η X
    ; nat = λ f → sym (ass _ _ _) ∙ cong (_∘ _) (α .nat f)
      ∙ (ass _ _ _) ∙ cong (_ ∘_) (β .nat f) ∙ sym (ass _ _ _)
    }
  ; idl = λ α → Nat≡ (λ i X → idl (α .η X) i)
  ; idr = λ α → Nat≡ (λ i X → idr (α .η X) i)
  ; ass = λ α β γ → Nat≡ (λ i X → ass (α .η X) (β .η X) (γ .η X) i)
  }
  where
    open Cat ⟦ B ⟧Cat
    open Nat

B : ⟦ (* ⇒ *) ⇒ * ⇒ * ⟧T
B F X = X × F (F X)

BB : ⟦ (* ⇒ *) ⇒ * ⇒ * ⟧Func B
BB = B₀ , {!FuncB!} -- 
  where
  open Func
  
  B₀ : (F : Type → Type) → ⟦ * ⇒ * ⟧Func F → ⟦ * ⇒ * ⟧Func (B F)
  B₀ F (_ , record { F₁ = F₁ ; F-id = F-id ; F-∘ = F-∘ })
    = _ , record
    { F₁ = λ (lift f) → lift (λ (x , ffx) → f x , lower (F₁ (F₁ (lift f))) ffx)
    ; F-id = λ i → lift (λ (x , ffx) → x , {!!})
    }
    {-
    { F₁ = λ{ f (x , ffx) → f x , F₁ (F₁ f) ffx }
    ; F-id = λ i (x , ffx) → x , (cong F₁ F-id ∙ F-id) i ffx
    ; F-∘ = λ f g i (x , ffx) → f (g x) , (cong F₁ (F-∘ f g) ∙ F-∘ (F₁ f) (F₁ g)) i ffx
    -}


{-
  FuncB : Func ⟦ * ⇒ * ⟧Cat ⟦ * ⇒ * ⟧Cat _
  FuncB .F₁ {F , _ , FF} {G , _ , GG} record { η = η ; nat = nat }
    = record
    { η = λ (X , _) (x , ffx) → x , η (G X , lift tt) (F₁ FF (η (X , lift tt)) ffx)
    ; nat = λ f i (x , ffx) → f x , aux f i ffx
    }
    where
      open Cat ⟦ * ⟧Cat
      aux : {X Y : Type} (f : X → Y)
        → F₁ GG (F₁ GG f) ∘ η (G X , lift tt) ∘ F₁ FF (η (X , lift tt))
        ≡ η (G Y , lift tt) ∘ F₁ FF (η (Y , lift tt)) ∘ F₁ FF (F₁ FF f)
      aux {X} {Y} f =
        F₁ GG (F₁ GG f) ∘ η (G X , lift tt) ∘ F₁ FF (η (X , lift tt))
          ≡⟨ cong (F₁ GG (F₁ GG f) ∘_) (sym (nat (η (X , lift tt)))) ⟩
        F₁ GG (F₁ GG f) ∘ F₁ GG (η (X , lift tt)) ∘ η (F X , lift tt)
          ≡⟨ cong (_∘ η (F X , lift tt)) (sym (F-∘ GG (F₁ GG f) (η (X , lift tt)))) ⟩
        F₁ GG (F₁ GG f ∘ η (X , lift tt)) ∘ η (F X , lift tt)
          ≡⟨ cong (_∘ η (F X , lift tt)) (cong (F₁ GG) (nat f)) ⟩
        F₁ GG (η (Y , lift tt) ∘ F₁ FF f) ∘ η (F X , lift tt)
          ≡⟨ cong (_∘ η (F X , lift tt)) (F-∘ GG (η (Y , lift tt)) (F₁ FF f)) ⟩
        F₁ GG (η (Y , lift tt)) ∘ F₁ GG (F₁ FF f) ∘ η (F X , lift tt)
          ≡⟨ cong (F₁ GG (η (Y , lift tt)) ∘_) (nat (F₁ FF f)) ⟩
        F₁ GG (η (Y , lift tt)) ∘ η (F Y , lift tt) ∘ F₁ FF (F₁ FF f)
          ≡⟨ cong (_∘ F₁ FF (F₁ FF f)) (nat (η (Y , lift tt))) ⟩
        η (G Y , lift tt) ∘ F₁ FF (η (Y , lift tt)) ∘ F₁ FF (F₁ FF f)
          ∎

  FuncB .F-id {F , _ , FF} = Nat≡ (λ i (X , _) (x , ffx) → x , F-id FF i ffx)

  FuncB .F-∘ {F , _ , FF} {G , _ , GG} {H , _ , HH}
    record { η = η₁ ; nat = nat₁ }
    record { η = η₂ ; nat = nat₂ }
    = Nat≡ (λ i (X , _) (x , ffx) → x , aux i ffx)
    where
      open Cat ⟦ * ⟧Cat
      aux : {X : Type}
        → η₁ (H X , lift tt) ∘ η₂ (H X , lift tt) ∘ F₁ FF(η₁ (X , lift tt) ∘ η₂ (X , lift tt))
        ≡ η₁ (H X , lift tt) ∘ F₁ GG (η₁ (X , lift tt)) ∘ η₂ (G X , lift tt) ∘ F₁ FF (η₂ (X , lift tt))
      aux {X} =
        η₁ (H X , lift tt) ∘ η₂ (H X , lift tt) ∘ F₁ FF (η₁ (X , lift tt) ∘ η₂ (X , lift tt))
          ≡⟨ cong ((η₁ (H X , lift tt) ∘ η₂ (H X , lift tt)) ∘_) (F-∘ FF (η₁ (X , lift tt)) (η₂ (X , lift tt))) ⟩
        η₁ (H X , lift tt) ∘ η₂ (H X , lift tt) ∘ F₁ FF (η₁ (X , lift tt)) ∘ F₁ FF (η₂ (X , lift tt))
          ≡⟨ cong (η₁ (H X , lift tt) ∘_) (cong (_∘ F₁ FF (η₂ (X , lift tt))) (sym (nat₂ (η₁ (X , lift tt))))) ⟩
        η₁ (H X , lift tt) ∘ F₁ GG (η₁ (X , lift tt)) ∘ η₂ (G X , lift tt) ∘ F₁ FF (η₂ (X , lift tt)) ∎
-}
