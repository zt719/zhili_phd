{-# OPTIONS --type-in-type #-}

module Cont.HCont where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

{- Syntax -}

infixr 20 _⇒_
data Ty : Set where
  ∘ : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

infixl 5 _▹_
data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

variable Γ Δ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y : Var Γ A

data Nf : Con → Ty → Set

record Ne (Γ : Con) (B : Ty) : Set

data Sp : Con → Ty → Ty → Set

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ ∘ → Nf Γ ∘

record Ne Γ B where
  inductive
  field
    S : Set
    P : S → Var Γ A → Set
    R : (s : S) (x : Var Γ A) (p : P s x) → Sp Γ A B

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

HCont : Ty → Set
HCont A = Nf ∙ A

{- Example -}

H : (Set → Set) → (Set → Set)
H F X = X × F (F X)

H-Nf : Nf ∙ ((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘)
H-Nf = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ ∘ ⇒ ∘ ▹ ∘

  X-S : Set
  X-S = ⊤

  X-P : X-S → Var Γ₀ A → Set
  X-P tt vz = ⊤
  X-P tt (vs vz) = ⊥

  X-R : (s : X-S) (x : Var Γ₀ A) → X-P s x → Sp Γ₀ A ∘
  X-R tt vz tt = ε
  X-R tt (vs vz) ()

  X-Nf : Nf Γ₀ ∘
  X-Nf = ne (record { S = X-S ; P = X-P ; R = X-R })
  ---
  FX-S : Set
  FX-S = ⊤

  FX-P : FX-S → Var Γ₀ A → Set
  FX-P tt vz = ⊥
  FX-P tt (vs vz) = ⊤

  FX-R : (s : FX-S) (x : Var Γ₀ A) → FX-P s x → Sp Γ₀ A ∘
  FX-R tt (vs vz) tt = X-Nf , ε
    
  FX-Nf : Nf Γ₀ ∘
  FX-Nf = ne (record { S = FX-S ; P = FX-P ; R = FX-R })
  ---
  S : Set
  S = ⊤
  
  P : S → Var Γ₀ A → Set
  P tt vz = ⊤
  P tt (vs vz) = ⊤

  R : (s : S) (x : Var Γ₀ A) (p : P s x) → Sp Γ₀ A ∘
  R tt vz tt = ε
  R tt (vs vz) p = FX-Nf , ε

H-HCont : HCont ((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘)
H-HCont = H-Nf

{- Semantics -}

⟦_⟧T : Ty → Set
⟦ ∘ ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Con → Set
⟦ ∙ ⟧C = ⊤
⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ vz ⟧v (γ , a) = a
⟦ vs x ⟧v (γ , a) = ⟦ x ⟧v γ

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦_⟧ne : Ne Γ ∘ → ⟦ Γ ⟧C → Set
⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧C → ⟦ A ⟧T → ⟦ B ⟧T

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))

⟦ ε ⟧sp γ a = a
⟦ n , ns ⟧sp γ f = ⟦ ns ⟧sp γ (f (⟦ n ⟧nf γ))

⟦_⟧hcont : HCont A → ⟦ A ⟧T
⟦ x ⟧hcont = ⟦ x ⟧nf tt



{- Weakening -}

_-_ : (Γ : Con) → Var Γ A → Con
∙ - ()
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - (vs x) = (Γ - x) ▹ A

wkv : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

{- Variable Equality -}

data EqVar : Var Γ A → Var Γ B → Set where
  same : EqVar x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqVar x (wkv x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqVar x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
eq (vs x) (vs .x)          | same = same
eq (vs x) (vs .(wkv x y')) | diff .x y' = diff (vs x) (vs y')

{- Weakening Nf -}

wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B
wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B
wkSp : (x : Var Γ A) → Sp (Γ - x) B C → Sp Γ B C

wkNf x (lam t) = lam (wkNf (vs x) t)
wkNf x (ne e) = ne (wkNe x e)

wkNe {Γ} {A} {C} x record { S = S ; P = P ; R = R }
  = record { S = S ; P = P' ; R = R' }
  where
  P' : S → Var Γ B → Set
  P' s y with eq x y
  P' s .x | same = ⊥
  P' s y  | diff .x y' = P s y'

  R' : (s : S) (y : Var Γ B) → P' s y → Sp Γ B C
  R' s y p with eq x y
  R' s .x () | same
  R' s y p   | diff .x y' = wkSp x (R s y' p)

wkSp x ε = ε
wkSp x (n , ns) = wkNf x n , wkSp x ns

{- Auxiliary functions -}

app : Nf Γ (A ⇒ B) → Nf (Γ ▹ A) B
app (lam x) = x

appSp : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
appSp ε u = u , ε
appSp (n , ns) u = n , appSp ns u

{- η-expansion -}

nvar : Var Γ A → Nf Γ A
ne2nf : Ne Γ A → Nf Γ A

nvar {Γ} {B} x =
  ne2nf (record { S = S ; P = P ; R = R })
  where
  S : Set
  S = ⊤

  P : S → Var Γ A → Set
  P tt y with eq x y
  P tt .x | same = ⊤
  P tt y  | diff .x y' = ⊥

  R : (s : S) (y : Var Γ A) → P s y → Sp Γ A B
  R tt y p with eq x y
  R tt .x p | same = ε
  R tt y () | diff .x y'

ne2nf {Γ} {∘} x = ne x
ne2nf {Γ} {A ⇒ C} record { S = S ; P = P ; R = R } =
  lam (ne2nf (record { S = S ; P = P' ; R = R' }))
  where
  P' : S → Var (Γ ▹ A) B → Set
  P' s x = {!!}

  R' : (s : S) (x : Var (Γ ▹ A) B) → P' s x → Sp (Γ ▹ A) B C
  R' s x p = appSp (wkSp vz (R s {!!} p)) (nvar vz)

{- Another example -}

WOW : ((Set → Set) → Set → Set) → (Set → Set) → Set → Set
WOW H F X = H F X

WOW' : ((Set → Set) → Set → Set) → (Set → Set) → Set → Set
WOW' H F X = H (λ Y → F Y) X

WOW-Nf : Nf ∙ (((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘) ⇒ ((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘))
WOW-Nf = lam (lam (lam (ne (record { S = S ; P = P ; R = R }))))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ (∘ ⇒ ∘) ⇒ ∘ ⇒ ∘ ▹ ∘ ⇒ ∘ ▹ ∘

  F-Nf : Nf Γ₀ (∘ ⇒ ∘)
  F-Nf = lam (ne (record { S = S ; P = P ; R = R }))
    where
    Y-Nf : Nf (Γ₀ ▹ ∘) ∘
    Y-Nf = ne (record { S = S ; P = P ; R = R })
      where
      S : Set
      S = ⊤

      P : S → Var (Γ₀ ▹ ∘) A → Set
      P tt vz = ⊤
      P tt (vs _) = ⊥

      R : (s : S) (x : Var (Γ₀ ▹ ∘) A) → P s x → Sp (Γ₀ ▹ ∘) A ∘
      R tt vz tt = ε
    
    S : Set
    S = ⊤

    P : S → Var (Γ₀ ▹ ∘) A → Set
    P tt vz = ⊥
    P tt (vs vz) = ⊥
    P tt (vs (vs vz)) = ⊤
    P tt (vs (vs (vs vz))) = ⊥

    R : (s : S) (x : Var (Γ₀ ▹ ∘) A) → P s x → Sp (Γ₀ ▹ ∘) A ∘
    R tt (vs (vs vz)) tt = Y-Nf , ε
    R tt (vs (vs (vs vz))) ()

  X-Nf : Nf Γ₀ ∘
  X-Nf = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : S → Var Γ₀ A → Set
    P tt vz = ⊤
    P tt (vs x) = ⊥

    R : (s : S) (x : Var Γ₀ A) → P s x → Sp Γ₀ A ∘
    R tt vz tt = ε
  
  S : Set
  S = ⊤

  P : S → Var Γ₀ A → Set
  P tt vz = ⊥
  P tt (vs vz) = ⊥
  P tt (vs (vs vz)) = ⊤

  R : (s : S) (x : Var Γ₀ A) → P s x → Sp Γ₀ A ∘
  R tt (vs (vs vz)) tt = F-Nf , X-Nf , ε

