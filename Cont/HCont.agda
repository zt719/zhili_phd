module Cont.HCont where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Level renaming (zero to lzero; suc to lsuc)

{- Syntax -}

{- Ty & Ctx & Var -}

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

infixl 5 _▹_
data Ctx : Set where
  ∙   : Ctx
  _▹_ : Ctx → Ty → Ctx

variable Γ Δ Θ : Ctx

data Var : Ctx → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y : Var Γ A

{- Object -}

data Nf : Ctx → Ty → Set₁

record Ne (Γ : Ctx) (B : Ty) : Set₁

data Sp : Ctx → Ty → Ty → Set₁

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ * → Nf Γ *

variable t u w : Nf Γ A

record Ne Γ B where
  constructor _◃_◃_
  inductive
  field
    S : Set
    P : Var Γ A → S → Set
    R : (x : Var Γ A) (s : S) → P x s → Sp Γ A B

variable n m l : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

variable ts us ws : Sp Γ A B

HCont : Ty → Set₁
HCont A = Nf ∙ A

variable H J K : HCont A

{- Weakening -}

_-_ : (Γ : Ctx) → Var Γ A → Ctx
∙ - ()
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - (vs x) = (Γ - x) ▹ A

wkv : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

{- Variable (Heterogeneous) Equality -}

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

wkNe {Γ} {A} {C} x (S ◃ P ◃ R) = S ◃ P' ◃ R'
  where
  P' : Var Γ B → S → Set
  P' y  s with eq x y
  P' .x s | same = ⊥
  P' y  s | diff .x y' = P y' s

  R' : (y : Var Γ B) (s : S) → P' y s → Sp Γ B C
  R' y s p with eq x y
  R' y s p | diff .x y' = wkSp x (R y' s p)

wkSp x ε = ε
wkSp x (n , ns) = wkNf x n , wkSp x ns

{- Auxiliary functions -}

appSp : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
appSp ε u = u , ε
appSp (n , ns) u = n , appSp ns u

{- η-expansion -}

nvar : Var Γ A → Nf Γ A
ne2nf : Ne Γ A → Nf Γ A

nvar {Γ} {B} x = ne2nf (S ◃ P ◃ R)
  where
  S : Set
  S = ⊤

  P : Var Γ A → S → Set
  P y  tt with eq x y
  P .x tt | same = ⊤
  P y  tt | diff .x y' = ⊥

  R : (y : Var Γ A) (s : S) → P y s → Sp Γ A B
  R y tt p with eq x y
  R .x tt p | same = ε
  R y tt () | diff .x y'

ne2nf {Γ} {*} x = ne x
ne2nf {Γ} {A ⇒ C} (S ◃ P ◃ R) =  lam (ne2nf (S ◃ P' ◃ R'))
  where
  P' : Var (Γ ▹ A) B → S → Set
  P' vz s = ⊥
  P' (vs x) s = P x s

  R' : (x : Var (Γ ▹ A) B) (s : S) → P' x s → Sp (Γ ▹ A) B C
  R' vz s ()
  R' (vs x) s p = appSp (wkSp vz (R x s p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

(lam t) [ x := u ] = lam (t [ vs x := wkNf vz u ])
(ne {Γ} (S ◃ P ◃ R)) [ x := u ] = ne (S ◃ P' ◃ R')
  where
  P' : Var (Γ - x) A → S → Set
  P' y s = P (wkv x y) s

  R' : (y : Var (Γ - x) A) (s : S) → P' y s → Sp (Γ - x) A *
  R' y s p = R (wkv x y) s p < x := u >
  
ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

t ◇ ε = t
t ◇ (u , us) = napp t u ◇ us

napp (lam t) u = t [ vz := u ]

{- Semantics -}

⟦_⟧T : Ty → Set₁
⟦ * ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Ctx → Set₁
⟦ ∙ ⟧C = Lift (lsuc lzero) ⊤
⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ vz ⟧v (γ , a) = a
⟦ vs x ⟧v (γ , a) = ⟦ x ⟧v γ

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T

⟦_⟧ne : Ne Γ * → ⟦ Γ ⟧C → Set

⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧C → ⟦ A ⟧T → ⟦ B ⟧T

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} (S ◃ P ◃ R) γ =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P x s) → ⟦ R x s p ⟧sp γ (⟦ x ⟧v γ))

⟦ ε ⟧sp γ a = a
⟦ ns , n ⟧sp γ f = ⟦ n ⟧sp γ (f (⟦ ns ⟧nf γ))

⟦_⟧ : HCont A → ⟦ A ⟧T
⟦ x ⟧ = ⟦ x ⟧nf (lift tt)

{- Algebraic Structure -}

_⊎Ne_ : Ne Γ B → Ne Γ B → Ne Γ B
_⊎Ne_ {Γ} {B} (S ◃ P ◃ R) (T ◃ Q ◃ L) = S' ◃ P' ◃ R'
  where
  S' : Set
  S' = S ⊎ T

  P' : Var Γ A → S' → Set
  P' x (inj₁ s) = P x s
  P' x (inj₂ t) = Q x t

  R' : (x : Var Γ A) (s : S') → P' x s → Sp Γ A B
  R' x (inj₁ s) p = R x s p
  R' x (inj₂ t) q = L x t q

_⊎Nf_ : Nf Γ A → Nf Γ A → Nf Γ A
lam t ⊎Nf lam u = lam (t ⊎Nf u)
ne n ⊎Nf ne m = ne (n ⊎Ne m)

_⊎C_ : HCont A → HCont A → HCont A
_⊎C_ = _⊎Nf_

_×Ne_ : Ne Γ B → Ne Γ B → Ne Γ B
_×Ne_ {Γ} {B} (S ◃ P ◃ R) (T ◃ Q ◃ L) = S' ◃ P' ◃ R'
  where
  S' : Set
  S' = S × T

  P' : Var Γ A → S' → Set
  P' x (s , t) = P x s ⊎ Q x t

  R' : (x : Var Γ A) (s : S') → P' x s → Sp Γ A B
  R' x (s , t) (inj₁ p) = R x s p
  R' x (s , t) (inj₂ q) = L x t q

_×Nf_ : Nf Γ A → Nf Γ A → Nf Γ A
lam t ×Nf lam u = lam (t ×Nf u)
ne n ×Nf ne m = ne (n ×Ne m)

_×C_ : HCont A → HCont A → HCont A
_×C_ = _×Nf_

zeroNf : Nf Γ A
zeroNf {Γ} {*} = ne (⊥ ◃ (λ x ()) ◃ (λ x ()))
zeroNf {Γ} {A ⇒ B} = lam zeroNf

zero : HCont A
zero = zeroNf

oneNf : Nf Γ A
oneNf {Γ} {*} = ne (⊤ ◃ (λ{ x tt → ⊥ }) ◃ λ{ x tt () })
oneNf {Γ} {A ⇒ B} = lam oneNf

one : HCont A
one = oneNf
