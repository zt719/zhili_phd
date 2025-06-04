module Cont.HCont where

open import Data.Empty
open import Data.Unit
open import Data.Product

open import Level

{- Syntax -}

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

private variable A B C : Ty

infixl 5 _▷_
data Con : Set where
  •   : Con
  _▷_ : Con → Ty → Con

private variable Γ Δ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▷ A) A
  vs : Var Γ A → Var (Γ ▷ B) A

private variable x y : Var Γ A

data Nf : Con → Ty → Set₁

record Ne (Γ : Con) (B : Ty) : Set₁

data Sp : Con → Ty → Ty → Set₁

data Nf where
  lam : Nf (Γ ▷ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ * → Nf Γ *

private variable t u : Nf Γ A

record Ne Γ B where
  inductive
  field
    S : Set
    P : S → Var Γ A → Set
    R : (s : S) (x : Var Γ A) → P s x → Sp Γ A B

private variable m n : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

private variable ts us : Sp Γ A B

HCont : Ty → Set₁
HCont A = Nf • A

{- Semantics -}

⟦_⟧T : Ty → Set₁
⟦ * ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Con → Set₁
⟦ • ⟧C = Lift (suc zero) ⊤
⟦ Γ ▷ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ vz ⟧v (γ , a) = a
⟦ vs x ⟧v (γ , a) = ⟦ x ⟧v γ

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T

⟦_⟧ne : Ne Γ * → ⟦ Γ ⟧C → Set
-- record ⟦_⟧ne (_ : Ne Γ *) (γ : ⟦ Γ ⟧C) : Set

⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧C → ⟦ A ⟧T → ⟦ B ⟧T

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))

{-
{-# NO_POSITIVITY_CHECK #-}
record ⟦_⟧ne {Γ} n γ where
  inductive
  open Ne n
  field
    s : S
    p : {A : Ty} (x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ)
-}

⟦ ε ⟧sp γ a = a
⟦ n , ns ⟧sp γ f = ⟦ ns ⟧sp γ (f (⟦ n ⟧nf γ))

⟦_⟧ : HCont A → ⟦ A ⟧T
⟦ x ⟧ = ⟦ x ⟧nf (lift tt)

{- Weakening -}

_-_ : (Γ : Con) → Var Γ A → Con
• - ()
(Γ ▷ A) - vz = Γ
(Γ ▷ A) - (vs x) = (Γ - x) ▷ A

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

ne2nf {Γ} {*} x = ne x
ne2nf {Γ} {A ⇒ C} record { S = S ; P = P ; R = R } =
  lam (ne2nf (record { S = S ; P = P' ; R = R' }))
  where
  P' : S → Var (Γ ▷ A) B → Set
  P' s vz = ⊥
  P' s (vs x) = P s x

  R' : (s : S) (x : Var (Γ ▷ A) B) → P' s x → Sp (Γ ▷ A) B C
  R' s vz ()
  R' s (vs x) p = appSp (wkSp vz (R s x p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

lam t [ x := u ] = lam (t [ vs x := wkNf vz u ])
ne {Γ} record { S = S ; P = P ; R = R } [ x := u ] =
  ne (record { S = S ; P = P' ; R = R' })
  where
  P' : S → Var (Γ - x) A → Set
  P' s y = P s (wkv x y)

  R' : (s : S) (y : Var (Γ - x) A) → P' s y → Sp (Γ - x) A *
  R' s y p = R s (wkv x y) p < x := u >
  
ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

t ◇ ε = t
t ◇ (u , us) = napp t u ◇ us

napp (lam t) u = t [ vz := u ]
