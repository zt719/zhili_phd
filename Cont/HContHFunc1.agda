module Cont.HContHFunc1 where

open import Data.Empty
open import Data.Unit
open import Data.Product

open import Level

{- Categories, Functors, Natural Transformation -}

record Cat (Obj : Set₁) : Set₂ where
  infixr 9 _∘_
  field
    Hom : Obj → Obj → Set₁
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z

record Func {A B : Set₁} (ℂ : Cat A) (𝔻 : Cat B) (F : A → B) : Set₁ where
  open Cat
  field
    F₁ : ∀ {X Y} → Hom ℂ X Y → Hom 𝔻 (F X) (F Y)

record Nat {A B : Set₁} (ℂ : Cat A) (𝔻 : Cat B)
  (F G : A → B) (FF : Func ℂ 𝔻 F) (GG : Func ℂ 𝔻 G) : Set₁ where
  open Cat
  open Func
  field
    η : ∀ X → Hom 𝔻 (F X) (G X)

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

private variable t u w : Nf Γ A

record Ne Γ B where
  inductive
  field
    S : Set
    P : Var Γ A → S → Set
    R : (x : Var Γ A) (s : S) → P x s → Sp Γ A B

private variable n m : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

private variable ts us ws : Sp Γ A B

HCont : Ty → Set₁
HCont A = Nf • A

{- Morphism -}

data NfHom : {Γ : Con} {A : Ty} (t u : Nf Γ A) → Set₁

record NeHom (n m : Ne Γ A) : Set₁

data SpHom : {Γ : Con} {A B : Ty} (t u : Sp Γ A B) → Set₁

data NfHom where
  lam : NfHom t u → NfHom (lam t) (lam u)
  ne  : NeHom n m → NfHom (ne n) (ne m)

data SpHom where
  ε   : SpHom {Γ} {A} ε ε
  _,_ : NfHom t u → SpHom ts us → SpHom (t , ts) (u , us)
 
record NeHom {Γ} {B} n m where
  inductive
  open Ne
  field
    f : n .S → m .S
    g : (x : Var Γ A) (s : n .S) → m .P x (f s) → n .P x s
    h : (x : Var Γ A) (s : n .S) (p : m .P x (f s))
      → SpHom (n .R x s (g x s p)) (m .R x (f s) p)

HContHom : HCont A → HCont A → Set₁
HContHom = NfHom {•}

idNfHom : {t : Nf Γ A} → NfHom t t
idNeHom : {n : Ne Γ A} → NeHom n n
idSpHom : {ts : Sp Γ A B} → SpHom ts ts

idNfHom {t = lam t} = lam idNfHom
idNfHom {t = ne x} = ne idNeHom

idNeHom = record { f = λ s → s ; g = λ x s p → p ; h = λ x s p → idSpHom }

idSpHom {ts = ε} = ε
idSpHom {ts = t , ts} = idNfHom , idSpHom

idHContHom : {H : HCont A} → HContHom H H
idHContHom = idNfHom

{- Weakening -}

_-_ : (Γ : Con) → Var Γ A → Con
• - ()
(Γ ▷ A) - vz = Γ
(Γ ▷ A) - (vs x) = (Γ - x) ▷ A

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

wkNe {Γ} {A} {C} x record { S = S ; P = P ; R = R }
  = record { S = S ; P = P' ; R = R' }
  where
  P' : Var Γ B → S → Set
  P' y  s with eq x y
  P' .x s | same = ⊥
  P' y  s | diff .x y' = P y' s

  R' : (y : Var Γ B) (s : S) → P' y s → Sp Γ B C
  R' y  s p with eq x y
  R' y  s p | diff .x y' = wkSp x (R y' s p)

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

  P : Var Γ A → S → Set
  P y  tt with eq x y
  P .x tt | same = ⊤
  P y  tt | diff .x y' = ⊥

  R : (y : Var Γ A) (s : S) → P y s → Sp Γ A B
  R y tt p with eq x y
  R .x tt p | same = ε
  R y tt () | diff .x y'

ne2nf {Γ} {*} x = ne x
ne2nf {Γ} {A ⇒ C} record { S = S ; P = P ; R = R } =
  lam (ne2nf (record { S = S ; P = P' ; R = R' }))
  where
  P' : Var (Γ ▷ A) B → S → Set
  P' vz s = ⊥
  P' (vs x) s = P x s

  R' : (x : Var (Γ ▷ A) B) (s : S) → P' x s → Sp (Γ ▷ A) B C
  R' vz s ()
  R' (vs x) s p = appSp (wkSp vz (R x s p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

(lam t) [ x := u ] = lam (t [ vs x := wkNf vz u ])
(ne {Γ} record { S = S ; P = P ; R = R }) [ x := u ] =
  ne (record { S = S ; P = P' ; R = R' })
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

_$_ : HCont (A ⇒ B) → HCont A → HCont B
_$_ = napp

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

⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧C → ⟦ A ⟧T → ⟦ B ⟧T

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P x s) → ⟦ R x s p ⟧sp γ (⟦ x ⟧v γ))

⟦ ε ⟧sp γ a = a
⟦ ns , n ⟧sp γ f = ⟦ n ⟧sp γ (f (⟦ ns ⟧nf γ))

⟦_⟧₀ : HCont A → ⟦ A ⟧T
⟦ x ⟧₀ = ⟦ x ⟧nf (lift tt)

{- Functoriality -}

⟦_⟧F : (A : Ty) → ⟦ A ⟧T → Set₁

⟦_⟧Cat : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧F)

⟦ * ⟧F X = Lift (suc zero) ⊤
⟦ A ⇒ B ⟧F H =
  Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧F F → ⟦ B ⟧F (H F)) ]
  Func ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (F , FF) → H F , HH F FF)

⟦ * ⟧Cat = record
  { Hom = λ (X , lift tt) (Y , lift tt) → Lift (suc zero) (X → Y)
  ; id = lift (λ x → x)
  ; _∘_ = λ{ (lift f) (lift g) → lift (λ x → f (g x)) }
  }
⟦ A ⇒ B ⟧Cat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG
  ; id = record { η = λ X → id }
  ; _∘_ = λ α β → record { η = λ X → α .η X ∘ β .η X }
  }
  where
    open Cat ⟦ B ⟧Cat
    open Nat

HFunc : (A : Ty) → Set₁
HFunc A = Σ ⟦ A ⟧T ⟦ A ⟧F

⟦_⟧₁ : (t : HCont A) → ⟦ A ⟧F ⟦ t ⟧₀
⟦_⟧₁ {A ⇒ B} (lam t) = (λ F FF → {!!}) , {!!}
⟦ ne x ⟧₁ = lift tt

⟦_⟧ : HCont A → HFunc A
⟦ t ⟧ = ⟦ t ⟧₀ , ⟦ t ⟧₁
