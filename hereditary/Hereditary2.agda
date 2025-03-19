module Hereditary2 where

data Ty : Set where
  ∘   : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

variable Γ Δ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y z : Var Γ A

data Tm : Con → Ty → Set where
  var : Var Γ A → Tm Γ A
  lam : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

variable t u : Tm Γ A

_-_ : (Γ : Con) → Var Γ A → Con
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - vs x = (Γ - x) ▹ A

wkVar : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkVar vz y = vs y
wkVar (vs x) vz = vz
wkVar (vs x) (vs y) = vs (wkVar x y)

wkTm : (x : Var Γ A) → Tm (Γ - x) B → Tm Γ B
wkTm x (var v) = var (wkVar x v)
wkTm x (lam t) = lam (wkTm (vs x) t)
wkTm x (app t u) = app (wkTm x t) (wkTm x u)

data EqVar : Var Γ A → Var Γ B → Set where
  same : EqVar x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqVar x (wkVar x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqVar x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
... | same = same
... | diff .x y = diff (vs x) (vs y)

data Nf : Con → Ty → Set

data Ne : Con → Ty → Set

data Sp : Con → Ty → Ty → Set

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ ∘ → Nf Γ ∘

data Ne where
  _,_ : Var Γ A → Sp Γ A B → Ne Γ B

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

embNf : Nf Γ A → Tm Γ A
embNe : Ne Γ A → Tm Γ A
embSp : Sp Γ A B → Tm Γ A → Tm Γ B

embNf (lam n) = lam (embNf n)
embNf (ne e) = embNe e

embNe (v , s) = embSp s (var v)

embSp ε t = t
embSp (n , ns) t = embSp ns (app t (embNf n))

wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B
wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B
wkSp : (x : Var Γ A) → Sp (Γ - x) B C → Sp Γ B C

wkNf x (lam n) = lam (wkNf (vs x) n)
wkNf x (ne e) = ne (wkNe x e)

wkNe x (v , ns) = wkVar x v , wkSp x ns

wkSp x ε = ε
wkSp x (n , ns) = wkNf x n , wkSp x ns

appSp : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
appSp ε n = n , ε
appSp (t , ts) n = t , appSp ts n

nvar : Var Γ A → Nf Γ A
ne2nf : Ne Γ A → Nf Γ A

ne2nf {A = ∘} e = ne e
ne2nf {A = A ⇒ B} (v , ns) =
  lam (ne2nf (vs v , appSp (wkSp vz ns) (nvar vz)))

nvar x = ne2nf (x , ε)

-----



_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B
_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C
_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B
napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

(lam t) [ x := u ] = lam (t [ vs x := wkNf vz u ])
(ne (y , ts)) [ x := u ] with eq x y
... | same = u ◇ (ts < x := u >)
... | diff .x y' = ne (y' , (ts < x := u >))

ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

t ◇ ε = t
t ◇ (u , us) = napp t u ◇ us

napp (lam t) u = t [ vz := u ]

nf : Tm Γ A → Nf Γ A
nf (var x) = nvar x
nf (lam t) = lam (nf t)
nf (app t u) = napp (nf t) (nf u)

-- λf.λz.f ((λx.f x) z)
ex0 : Tm ∙ ((∘ ⇒ ∘) ⇒ (∘ ⇒ ∘))
ex0 = lam (lam (app (var (vs vz)) (app (lam (app (var (vs (vs vz))) (var vz))) (var vz))))

-- λf.λz.f z
ex1 : Tm ∙ ((∘ ⇒ ∘) ⇒ (∘ ⇒ ∘))
ex1 = lam (var vz)
