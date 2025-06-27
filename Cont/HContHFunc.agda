{-# OPTIONS --cubical --type-in-type #-}

module Cont.HContHFunc where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma

{- Categories & Functors & Natural Transformations -}

record Cat (Obj : Type) : Type where
  infixr 9 _∘_
  field
    Hom : Obj → Obj → Type
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    ass : ∀ {W X Y Z} (f : Hom X W) (g : Hom Y X) (h : Hom Z Y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

record Func {A B : Type} (ℂ : Cat A) (𝔻 : Cat B) (F : A → B) : Type where
  open Cat
  field
    F₁ : ∀ {X Y} → Hom ℂ X Y → Hom 𝔻 (F X) (F Y)
    F-id : ∀ {X} → F₁ {X} (ℂ .id) ≡ 𝔻 .id
    F-∘ : ∀ {X Y Z} (f : Hom ℂ Y Z) (g : Hom ℂ X Y)
          → F₁ (ℂ ._∘_ f g ) ≡ 𝔻 ._∘_ (F₁ f) (F₁ g)

record Nat {A B : Type} (ℂ : Cat A) (𝔻 : Cat B)
  (F G : A → B) (FF : Func ℂ 𝔻 F) (GG : Func ℂ 𝔻 G) : Type where
  open Cat
  open Func
  field
    η : ∀ X → Hom 𝔻 (F X) (G X)
    nat : ∀ {X Y} (f : Hom ℂ X Y)
      → 𝔻 ._∘_ (GG .F₁ f) (η X) ≡ 𝔻 ._∘_ (η Y) (FF .F₁ f)

postulate
  Nat≡ : {A B : Type} {ℂ : Cat A} {𝔻 : Cat B} {F G : A → B}
    → {FF : Func ℂ 𝔻 F} {GG : Func ℂ 𝔻 G}
    → {α β : Nat ℂ 𝔻 F G FF GG}
    → α .Nat.η ≡ β .Nat.η → α ≡ β

{- Syntax of Types -}

data Ty : Type where
  * : Ty
  _⇒_ : Ty → Ty → Ty

private variable A B C : Ty

⟦_⟧T : Ty → Type
⟦ * ⟧T = Type
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

{- Higher-order Functoriality -}

⟦_⟧T₁ : (A : Ty) → ⟦ A ⟧T → Type

⟦_⟧Cat : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧T₁)

⟦ * ⟧T₁ X = ⊤
⟦ A ⇒ B ⟧T₁ H =
  Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧T₁ F → ⟦ B ⟧T₁ (H F)) ]
  Func ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (F , FF) → H F , HH F FF)

⟦ * ⟧Cat = record
  { Hom = λ (X , _) (Y , _) → X → Y
  ; id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; idl = λ f → refl
  ; idr = λ f → refl
  ; ass = λ f g h → refl
  }
⟦ A ⇒ B ⟧Cat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG
  ; id = record { η = λ X → id ; nat = λ f → idr _ ∙ sym (idl _) }
  ; _∘_ = λ{ record { η = η₁ ; nat = nat₁ } record { η = η₂ ; nat = nat₂ }
    → record { η = λ X → η₁ X ∘ η₂ X ; nat = λ f → sym (ass _ _ _) ∙ cong (_∘ _) (nat₁ f)
              ∙ (ass _ _ _) ∙ cong (_ ∘_) (nat₂ f) ∙ sym (ass _ _ _) } }
  ; idl = λ α → Nat≡ (λ i X → idl (α .Nat.η X) i)
  ; idr = λ α → Nat≡ (λ i X → idr (α .Nat.η X) i)
  ; ass = λ α β γ → Nat≡ (λ i X → ass (α .Nat.η X) (β .Nat.η X) (γ .Nat.η X) i)
  }
  where
    open Cat ⟦ B ⟧Cat

HFunc : Ty → Type
HFunc A = Σ ⟦ A ⟧T ⟦ A ⟧T₁

infixl 5 _▹_
data Con : Type where
  •   : Con
  _▹_ : Con → Ty → Con

private variable Γ Δ : Con

data Var : Con → Ty → Type where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

private variable x y : Var Γ A

data Nf : Con → Ty → Type₁

record Ne (Γ : Con) (B : Ty) : Type₁

data Sp : Con → Ty → Ty → Type₁

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ * → Nf Γ *

private variable t u : Nf Γ A

record Ne Γ B where
  inductive
  field
    S : Type
    P : S → Var Γ A → Type
    R : (s : S) (x : Var Γ A) → P s x → Sp Γ A B

private variable m n : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

private variable ts us : Sp Γ A B

HCont : Ty → Type₁
HCont A = Nf • A

{- Semantics of Higher Containers -}

⟦_⟧C : Con → Type₁
⟦ • ⟧C = ⊤
⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ vz ⟧v (γ , a) = a
⟦ vs x ⟧v (γ , a) = ⟦ x ⟧v γ

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T

⟦_⟧ne : Ne Γ * → ⟦ Γ ⟧C → Type

⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧C → ⟦ A ⟧T → ⟦ B ⟧T

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))

⟦ ε ⟧sp γ a = a
⟦ n , ns ⟧sp γ f = ⟦ ns ⟧sp γ (f (⟦ n ⟧nf γ))

⟦_⟧ : HCont A → ⟦ A ⟧T
⟦ x ⟧ = ⟦ x ⟧nf tt

{- Functoriality -}

⟦_⟧C₁ : (Γ : Con) (γ : ⟦ Γ ⟧C) → Set
⟦ • ⟧C₁ tt = ⊤
⟦ Γ ▹ A ⟧C₁ (γ , a) = ⟦ Γ ⟧C₁ γ × ⟦ A ⟧T₁ a

⟦_⟧nf₁ : (t : Nf Γ A) (γ : ⟦ Γ ⟧C) (γ₁ : ⟦ Γ ⟧C₁ γ) → ⟦ A ⟧T₁ (⟦ t ⟧nf γ)
⟦ lam t ⟧nf₁ γ γ₁ = (λ a a₁ → ⟦ t ⟧nf₁ (γ , a) (γ₁ , a₁))
  , record
  { F₁ = λ x → {!!}
  ; F-id = {!!}
  ; F-∘ = {!!}
  }
  where open Cat
⟦ ne x ⟧nf₁ γ γ₁ = tt

{-
⟦_⟧ne₁ : (n : Ne Γ *) (x : Var Γ A) → Func {!!} {!!} {!!}
⟦_⟧ne₁ {Γ} record { S = S ; P = P ; R = R } x = record
  { F₁ = {!!} ; F-id = {!!} ; F-∘ = {!!} }
-}

⟦_⟧₁ : (t : HCont A) → ⟦ A ⟧T₁ (⟦ t ⟧)
⟦ t ⟧₁ = ⟦ t ⟧nf₁ tt tt
