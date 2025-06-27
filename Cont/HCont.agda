module Cont.HCont where

open import Data.Empty
open import Data.Unit
open import Data.Product

open import Level

{- Syntax -}

{- Ty & Con & Var -}

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

{- Object -}

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

private variable n m l : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

private variable ts us ws : Sp Γ A B

HCont : Ty → Set₁
HCont A = Nf • A

private variable H J K : HCont A

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

idNfHom : NfHom t t
idNeHom : NeHom n n
idSpHom : SpHom ts ts

idNfHom {t = lam t} = lam idNfHom
idNfHom {t = ne x} = ne idNeHom

idNeHom = record { f = λ s → s ; g = λ x s p → p ; h = λ x s p → idSpHom }

idSpHom {ts = ε} = ε
idSpHom {ts = t , ts} = idNfHom , idSpHom

idHContHom : HContHom H H
idHContHom = idNfHom

∘NfHom : NfHom u w → NfHom t u → NfHom t w
∘NeHom : NeHom m l → NeHom n m → NeHom n l
∘SpHom : SpHom us ws → SpHom ts us → SpHom ts ws

∘NfHom (lam α) (lam β) = lam (∘NfHom α β)
∘NfHom (ne e) (ne e') = ne (∘NeHom e e')

∘NeHom record { f = f ; g = g ; h = h }
  record { f = f₁ ; g = g₁ ; h = h₁ }
  = record
  { f = λ x → f (f₁ x)
  ; g = λ x s p → g₁ x s (g x (f₁ s) p)
  ; h = λ x s p → ∘SpHom (h x (f₁ s) p) (h₁ x s (g x (f₁ s) p))
  }

∘SpHom ε ε = ε
∘SpHom (t , ts) (u , us) = ∘NfHom t u , ∘SpHom ts us

∘HContHom : HContHom J K → HContHom H J → HContHom H K
∘HContHom = ∘NfHom

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

{-
wkNfHom : (x : Var Γ A) {t u : Nf (Γ - x) B} → NfHom t u → NfHom (wkNf x t) (wkNf x u)
wkNeHom : (x : Var Γ A) {n m : Ne (Γ - x) B} → NeHom n m → NeHom (wkNe x n) (wkNe x m)
wkSpHom : (x : Var Γ A) {ts us : Sp (Γ - x) B C} → SpHom ts us → SpHom (wkSp x ts) (wkSp x us)

wkNfHom x (lam α) = lam (wkNfHom (vs x) α)
wkNfHom x (ne e) = ne (wkNeHom x e)

wkNeHom x = {!!}
wkNeHom {Γ} {A} {B} x {n} {m} record { f = f ; g = g ; h = h }
  = record { f = f ; g = {!!} ; h = {!!} }
  where

wkSpHom x ε = ε
wkSpHom x (α , αs) = wkNfHom x α , wkSpHom x αs
-}

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

{-
_[_:=_]₁ : (t : Nf Γ B) (x : Var Γ A) {u w : Nf (Γ - x) A}
  → NfHom u w → NfHom (t [ x := u ]) (t [ x := w ])

_<_:=_>₁ : (ts : Sp Γ B C) (x : Var Γ A) {u w : Nf (Γ - x) A}
  → NfHom u w → SpHom (ts < x := u >) (ts < x := w >)

napp₁ : (t : Nf Γ (A ⇒ B)) → NfHom u w → NfHom (napp t u) (napp t w)

(lam t) [ x := α ]₁ = lam (t [ vs x := wkNfHom vz α ]₁)
_[_:=_]₁ (ne record { S = S ; P = P ; R = R }) x {u} {w} α = {!!}
--  = ne (record { f = λ s → s ; g = {!!} ; h = {!!} })

ε < x := α >₁ = ε
(t , ts) < x := α >₁ = (t [ x := α ]₁) , (ts < x := α >₁)

napp₁ (lam t) α = t [ vz := α ]₁

_$₁_ : (t : HCont (A ⇒ B)) → HContHom u w → HContHom (t $ u) (t $ w)
t $₁ α = napp₁ t α
-}

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

⟦_⟧ : HCont A → ⟦ A ⟧T
⟦ x ⟧ = ⟦ x ⟧nf (lift tt)

{-
⟦_⟧NfHom : {t u : Nf Γ A} → NfHom t u → (γ : ⟦ Γ ⟧C) → Set₁
⟦_⟧NfHom {Γ} {*} {t} {u} α γ = Lift (suc zero) (⟦ t ⟧nf γ → ⟦ u ⟧nf γ)
⟦_⟧NfHom {Γ} {A ⇒ B} {t} {u} (lam α) γ = (a : ⟦ A ⟧T) → ⟦ α ⟧NfHom (γ , a)

⟦_⟧Hom : {A : Ty} {t u : HCont A} (α : HContHom t u) → Set₁
⟦_⟧Hom = {!!}

{-
dom : Ty → Con
dom * = •
dom (A ⇒ B) = dom B ▷ A

appDom : ⟦ A ⟧T → ⟦ dom A ⟧C → Set
appDom {*} a (lift tt) = a
appDom {A ⇒ B} f (γ , a) = appDom (f a) γ

⟦_⟧nfHom : {t u : Nf Γ A} → NfHom t u → (γ : ⟦ Γ ⟧C) (δ : ⟦ dom A ⟧C)
  → appDom (⟦ t ⟧nf γ) δ → appDom (⟦ u ⟧nf γ) δ
  
⟦_⟧neHom : {m n : Ne Γ *} → NeHom m n → (γ : ⟦ Γ ⟧C)
  → ⟦ m ⟧ne γ → ⟦ n ⟧ne γ

⟦_⟧spHom : {ts us : Sp Γ A B} → SpHom ts us → (γ : ⟦ Γ ⟧C) (a : ⟦ A ⟧T) (δ : ⟦ dom B ⟧C)
  → appDom (⟦ ts ⟧sp γ a) δ → appDom (⟦ us ⟧sp γ a) δ

⟦ lam α ⟧nfHom γ (δ , a) = ⟦ α ⟧nfHom (γ , a) δ
⟦ ne e ⟧nfHom γ (lift tt) = ⟦ e ⟧neHom γ

⟦ record { f = f ; g = g ; h = h } ⟧neHom γ (s , k)
  = f s , λ x p → ⟦ h x s p ⟧spHom γ (⟦ x ⟧v γ) (lift tt) (k x (g x s p))

⟦ ε ⟧spHom γ a δ x = x
⟦ α , αs ⟧spHom γ f δ x = {!!}

⟦_⟧Hom : {H J : HCont A} → HContHom H J
  → (γ : ⟦ dom A ⟧C) → appDom ⟦ H ⟧ γ → appDom ⟦ J ⟧ γ
⟦ α ⟧Hom γ = ⟦ α ⟧nfHom (lift tt) γ

{-
⟦_⟧₁ : (H : HCont ((* ⇒ *) ⇒ (* ⇒ *)))
  → {F G : HCont (* ⇒ *)} (α : HContHom F G)
  → {X Y : HCont *} (f : HContHom X Y)
  → ⟦ H ⟧ ⟦ F ⟧ ⟦ X ⟧ → ⟦ H ⟧ ⟦ G ⟧ ⟦ Y ⟧
⟦ lam (lam (ne record { S = S ; P = P ; R = R })) ⟧₁ {F} {G} α {X} {Y} f (s , k)
  = s , λ{ vz p → {!!} ; (vs vz) p → {!!} }
-}
-}

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

{- Higher Functoriality -}

⟦_⟧Func : HCont A → Set₁
⟦_⟧Cat : (A : Ty) → Cat (Σ (HCont A) ⟦_⟧Func)

⟦_⟧Func {*} X = Lift (suc zero) ⊤
⟦_⟧Func {A ⇒ B} H =
  Σ[ HH ∈ ({F : HCont A} → ⟦ F ⟧Func → ⟦ H $ F ⟧Func) ]
  Func ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (F , FF) → H $ F , HH FF)

⟦ * ⟧Cat = record
  { Hom = λ (X , lift tt) (Y , lift tt) → HContHom X Y
  ; id = idHContHom
  ; _∘_ = ∘HContHom
  }

⟦ A ⇒ B ⟧Cat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (X , XX) → F $ X , FF XX) (λ (X , XX) → (G $ X) , GG XX) FFF GGG
  ; id = record { η = λ X → ⟦ B ⟧Cat .Cat.id }
  ; _∘_ = λ x x₁ → record { η = λ X → ⟦ B ⟧Cat .Cat._∘_ (x .Nat.η X) (x₁ .Nat.η X) }
  }
-}
{-
app₂ : HCont ((* ⇒ *) ⇒ * ⇒ *) → HCont (* ⇒ *) → HCont (* ⇒ *)
app₂
  (lam (lam (ne record { S = HS ; P = HP ; R = HR })))
  (lam (ne record { S = FS ; P = FP ; R = FR }))
  = lam (ne (record { S = {!!} ; P = {!!} ; R = {!!} }))
-}
