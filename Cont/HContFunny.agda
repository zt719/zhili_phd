module Cont.HContFunny where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base

{- Tys & Contexts & Variables -}

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

infixl 5 _▹_
data Con : Set where
  •   : Con
  _▹_ : Con → Ty → Con

variable Γ Δ Θ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y : Var Γ A

{- Normal Forms -}

infixr 4 _,_

data Nf : Con → Ty → Set₁

record Ne (Γ : Con) (B : Ty) : Set₁

data Sp : Con → Ty → Ty → Set₁

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

variable spr tql : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  
variable ts us ws : Sp Γ A B

HCont : Ty → Set₁
HCont = Nf •

ap : Nf Γ (A ⇒ B) → Nf (Γ ▹ A) B
ap (lam t) = t

en : Nf Γ * → Ne Γ *
en (ne spr) = spr

{- Variable Weakening & (Heterogeneous) Equality -}

_-_ : (Γ : Con) → Var Γ A → Con
• - ()
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - (vs x) = (Γ - x) ▹ A

wkv : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

data EqVar : Var Γ A → Var Γ B → Set where
  same : EqVar x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqVar x (wkv x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqVar x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
eq (vs x) (vs .x)          | same = same
eq (vs x) (vs .(wkv x y′)) | diff .x y′ = diff (vs x) (vs y′)

{- Normal Forms Weakening -}

wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B

wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B

wkSp : (x : Var Γ A) → Sp (Γ - x) B C → Sp Γ B C

wkNf x (lam t) = lam (wkNf (vs x) t)
wkNf x (ne spr) = ne (wkNe x spr)

wkNe {Γ} {A} {C} x (S ◃ P ◃ R) = S′ ◃ P′ ◃ R′
  where
  S′ : Set
  S′ = S
  
  P′ : Var Γ B → S → Set
  P′ y  s with eq x y
  P′ .x s | same = ⊥
  P′ y  s | diff .x y′ = P y′ s

  R′ : (y : Var Γ B) (s : S) → P′ y s → Sp Γ B C
  R′ y s p with eq x y
  R′ y s p | diff .x y′ = wkSp x (R y′ s p)

wkSp x ε = ε
wkSp x (t , ts) = wkNf x t , wkSp x ts

{- η-expansion -}

appSp : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
appSp ε u = u , ε
appSp (t , ts) u = t , appSp ts u

nvar : Var Γ A → Nf Γ A

ne2nf : Ne Γ A → Nf Γ A

nvar {Γ} {B} x = ne2nf (S ◃ P ◃ R)
  where
  S : Set
  S = ⊤

  P : Var Γ A → S → Set
  P y  tt with eq x y
  P .x tt | same = ⊤
  P y  tt | diff .x y′ = ⊥

  R : (y : Var Γ A) (s : S) → P y s → Sp Γ A B
  R y tt p with eq x y
  R .x tt p | same = ε
  R y tt () | diff .x y′

ne2nf {Γ} {*} spr = ne spr
ne2nf {Γ} {A ⇒ C} (S ◃ P ◃ R) = lam (ne2nf (S ◃ P′ ◃ R′))
  where
  P′ : Var (Γ ▹ A) B → S → Set
  P′ vz s = ⊥
  P′ (vs x) s = P x s

  R′ : (x : Var (Γ ▹ A) B) (s : S) → P′ x s → Sp (Γ ▹ A) B C
  R′ vz s ()
  R′ (vs x) s p = appSp (wkSp vz (R x s p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

lam t [ x := u ] = lam (t [ vs x := wkNf vz u ])
ne {Γ} (S ◃ P ◃ R) [ x := u ] = ne (S ◃ P′ ◃ R′)
  where
  P′ : Var (Γ - x) A → S → Set
  P′ y s = P (wkv x y) s
  
  R′ : (y : Var (Γ - x) A) (s : S) → P′ y s → Sp (Γ - x) A *
  R′ y s p = R (wkv x y) s p < x := u >

ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

⟦_⟧ : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B
⟦ lam t ⟧ u = t [ vz := u ]

{- Morphisms -}

data NfHom : (Γ : Con) → Nf Γ A → Nf Γ A → Set₁

record NeHom Γ {B} (spr tql : Ne Γ B) : Set₁

data SpHom : (Γ : Con) → Sp Γ A B → Sp Γ A B → Set₁

data NfHom where
  lam : NfHom (Γ ▹ A) t u → NfHom Γ (lam t) (lam u)
  ne  : NeHom Γ spr tql → NfHom Γ (ne spr) (ne tql)

record NeHom Γ {B} spr tql where
  constructor _◃_◃_
  inductive
  open Ne spr
  open Ne tql renaming (S to T; P to Q; R to L)
  field
    fS : S → T
    fP : (x : Var Γ A) (s : S) → Q x (fS s) → P x s
    fR : (x : Var Γ A) (s : S) (q : Q x (fS s))
      → SpHom Γ (R x s (fP x s q)) (L x (fS s) q)
       
data SpHom where
  ε   : SpHom Γ ts ts
  _,_ : NfHom Γ t u → SpHom Γ ts us → SpHom Γ (t , ts) (u , us)

HContHom : HCont A → HCont A → Set₁
HContHom = NfHom •

idNfHom : NfHom Γ t t
idNfHom {t = ne spr} = ne (id ◃ (λ x s → id) ◃ (λ x s q → ε))
idNfHom {t = lam t} = lam (idNfHom {t = t})

_∘nfHom_ : NfHom Γ u w → NfHom Γ t u → NfHom Γ t w
_∘spHom_ : SpHom Γ us ws → SpHom Γ ts us → SpHom Γ ts ws

lam f ∘nfHom lam g = lam (f ∘nfHom g)
ne (fS ◃ fP ◃ fR) ∘nfHom ne (gS ◃ gP ◃ gR) = ne (
  (fS ∘ gS)
  ◃ (λ x s → gP x s ∘ fP x (gS s))
  ◃ λ x s q → (fR x (gS s) q) ∘spHom gR x s (fP x (gS s) q)
  )

ε ∘spHom ε = ε
ε ∘spHom (g , gs) = g , gs
(f , fs) ∘spHom ε = f , fs
(f , fs) ∘spHom (g , gs) = (f ∘nfHom g) , (fs ∘spHom gs)

wkNfHom : (x : Var Γ A) {t u : Nf (Γ - x) B} → NfHom (Γ - x) t u → NfHom Γ (wkNf x t) (wkNf x u)

wkNeHom : (x : Var Γ A) {spr tql : Ne (Γ - x) B} → NeHom (Γ - x) spr tql → NeHom Γ (wkNe x spr) (wkNe x tql)

wkSpHom : (x : Var Γ A) {ts us : Sp (Γ - x) B C} → SpHom (Γ - x) ts us → SpHom Γ (wkSp x ts) (wkSp x us)

wkNfHom x (lam f) = lam (wkNfHom (vs x) f)
wkNfHom x (ne f) = ne (wkNeHom x f)

wkNeHom {Γ} x {S ◃ P ◃ R} {T ◃ Q ◃ L} (fS ◃ fP ◃ fR) = fS ◃ fP' ◃ fR'
  where
  open Ne (wkNe x (S ◃ P ◃ R)) renaming (S to S'; P to P'; R to R')
  open Ne (wkNe x (T ◃ Q ◃ L)) renaming (S to T'; P to Q'; R to L')

  fP' : (y : Var Γ A) (s' : S') → Q' y (fS s') → P' y s'
  fP' y s' q' with eq x y
  fP' .(wkv x y') s' q' | diff .x y' = fP y' s' q'

  fR' : (y : Var Γ A) (s' : S') (q' : Q' y (fS s')) → SpHom Γ (R' y s' (fP' y s' q')) (L' y (fS s') q')
  fR' y s' q' with eq x y
  fR' .(wkv x y') s' q' | diff .x y' = wkSpHom x (fR y' s' q')

wkSpHom x ε = ε
wkSpHom x (f , fs) = wkNfHom x f , wkSpHom x fs

{- Functorial -}

_[_:=_]₁ : (t : Nf Γ B) (x : Var Γ A) {u w : Nf (Γ - x) A}
  → NfHom (Γ - x) u w
  → NfHom (Γ - x) (t [ x := u ]) (t [ x := w ])
lam t [ x := u→w ]₁ = lam (t [ vs x := wkNfHom vz u→w ]₁)
ne (S ◃ P ◃ R) [ x := u→w ]₁ = ne (id ◃ (λ x s → id) ◃ (λ x s q → ε))

_<_:=_>₁ : (ts : Sp Γ B C) (x : Var Γ A) {u w : Nf (Γ - x) A}
  → NfHom (Γ - x) u w
  → SpHom (Γ - x) (ts < x := u >) (ts < x := w >)
ε < x := u→w >₁ = ε
(t , ts) < x := u→w >₁ = (t [ x := u→w ]₁) , (ts < x := u→w >₁)

⟦_⟧₁ : (t : Nf Γ (A ⇒ B)) → NfHom Γ u w → NfHom Γ (⟦ t ⟧ u) (⟦ t ⟧ w)
⟦ lam t ⟧₁ u→w = t [ vz := u→w ]₁

{-
open import Relation.Binary.PropositionalEquality

nf-id : (t : Nf (Γ ▹ A) B) → t [ vz := idNfHom {t = u} ]₁ ≡ idNfHom
nf-id {Γ} {A} {B ⇒ C} {u} (lam t) = cong lam {!!}
nf-id {Γ} {A} {B} {u} (ne x) = {!!}

napp-id : (t : Nf Γ (A ⇒ B)) → napp₁ t (idNfHom {t = u}) ≡ idNfHom
napp-id {Γ} {A} {B} {u} (lam t) = nf-id t
-}

{- Semantics -}

record Cat : Set₂ where
  field
    Obj : Set₁
    Hom : Obj → Obj → Set₁
    ID : ∀ {X} → Hom X X
    COMP : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z

record Func (ℂ 𝔻 : Cat) : Set₁ where
  open Cat
  field
    F : ℂ .Obj → 𝔻 .Obj
    F₁ : ∀ {X Y} → ℂ .Hom X Y → 𝔻 .Hom (F X) (F Y)

HCONT : (A : Ty) → Cat
HCONT A = record
  { Obj = HCont A
  ; Hom = HContHom
  ; ID = idNfHom
  ; COMP = _∘nfHom_
  }

⟦_⟧Ty : Ty → Set₁
⟦ * ⟧Ty = Set
⟦ A ⇒ B ⟧Ty = Func (HCONT A) (HCONT B)

⟦_⟧HCont : {A : Ty} → HCont A → ⟦ A ⟧Ty
⟦_⟧HCont {*} (ne (S ◃ P ◃ R)) = S
⟦_⟧HCont {A ⇒ B} H = record { F = ⟦ H ⟧ ; F₁ = ⟦ H ⟧₁ }

T : HCont (((* ⇒ *) ⇒ *) ⇒ (* ⇒ *) ⇒ *)
T = lam (lam (⟦ nvar vz ⟧ (⟦ nvar (vs vz) ⟧ (nvar vz))))

{-
postulate
  HW : Func (HCONT (A ⇒ A)) (HCONT A)

W : Func (HCONT (* ⇒ *)) (HCONT *)
W = ⟦ HW .Func.F T ⟧HCont
-}

HW : HCont (A ⇒ A) → HCont A
HW {A} (lam t) = {!!}
