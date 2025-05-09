{-# OPTIONS --cubical --type-in-type #-}

module Cont.HContHFunc where

open import Cubical.Foundations.Prelude hiding (_▷_)
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

{- Higher Functoriality -}

⟦_⟧Func : (A : Ty) → ⟦ A ⟧T → Type
⟦_⟧Cat : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧Func)

⟦ * ⟧Func X = ⊤
⟦ A ⇒ B ⟧Func H =
  Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧Func F → ⟦ B ⟧Func (H F)) ]
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
HFunc A = Σ[ F ∈ ⟦ A ⟧T ] ⟦ A ⟧Func F

{- Syntax of Contexts -}

infixl 5 _▷_

data Con : Type where
  •   : Con
  _▷_ : Con → Ty → Con

private variable Γ Δ : Con

{- Syntax of Higher Containers by Hereditary STLC -}

data Var : Con → Ty → Type where
  vz : Var (Γ ▷ A) A
  vs : Var Γ A → Var (Γ ▷ B) A

private variable x y : Var Γ A

data Nf : Con → Ty → Type₁

record Ne (Γ : Con) (B : Ty) : Type₁

data Sp : Con → Ty → Ty → Type₁

data Nf where
  lam : Nf (Γ ▷ A) B → Nf Γ (A ⇒ B)
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
⟦ Γ ▷ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

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

open import Cubical.Data.Empty
open import Cubical.Data.Bool

MaybeHCont : HCont (* ⇒ *)
MaybeHCont = lam (ne (record { S = S ; P = P ; R = R }))
  where
  S : Type
  S = Bool

  P : S → Var (• ▷ *) A → Type
  P false vz = ⊥
  P true vz = ⊤

  R : (s : S) (x : Var (• ▷ *) A) → P s x → Sp (• ▷ *) A *
  R true vz tt = ε

eq : (ts : Sp Γ * *) (γ : ⟦ Γ ⟧C) (X : Type) → ⟦ ts ⟧sp γ X ≡ X
eq ε γ X = refl

1⟦_⟧ : (c : HCont (* ⇒ *)) → ⟦ * ⇒ * ⟧Func ⟦ c ⟧
1⟦ lam (ne record { S = S ; P = P ; R = R }) ⟧ =
  (λ X _ → tt) , record
  { F₁ = λ{ {(X , tt)} {(Y , tt)} f (s , k) →
    s , λ{ vz p → transport (sym (eq (R s vz p) (tt , Y) Y)) (f (transport (eq (R s vz p) (tt , X) X) (k vz p))) } }
  ; F-id = λ{ {(X , tt)} i (s , k) → s , λ x p → {!!} }
  ; F-∘ = {!!}
  }

2⟦_⟧ : (hc : HCont ((* ⇒ *) ⇒ (* ⇒ *))) → ⟦ (* ⇒ *) ⇒ (* ⇒ *) ⟧Func ⟦ hc ⟧
2⟦ lam (lam (ne record { S = S ; P = P ; R = R })) ⟧ =
  (λ{ H (_ , record { F₁ = F₁ ; F-id = F-id ; F-∘ = F-∘ })
  → _ , record { F₁ = {!!} ; F-id = {!!} ; F-∘ = {!!} }}
  ) , record
  { F₁ = {!!}
  ; F-id = {!!}
  ; F-∘ = {!!}
  }

{-
⟦_⟧nf₁ : (t : Nf Γ A) (γ : ⟦ Γ ⟧C) → ⟦ A ⟧Func (⟦ t ⟧nf γ)

⟦ lam t ⟧nf₁ γ = (λ F x → ⟦ t ⟧nf₁ (γ , F)) ,
  record
  { F₁ = λ {(X , XX)} {(Y , YY)} α → {!!}
  ; F-id = {!!}
  ; F-∘ = {!!}
  }
  where open Cat
⟦ ne x ⟧nf₁ γ = {!!}


⟦_⟧₁ : (x : HCont A) → ⟦ A ⟧Func ⟦ x ⟧
⟦ x ⟧₁ = ⟦ x ⟧nf₁ tt
-}
