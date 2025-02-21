module Hereditary where

data Ty : Set where
  ∘ : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con

variable Γ Δ θ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ , A) A
  vs : Var Γ A → Var (Γ , B) A

variable x y z : Var Γ A

data Tm : Con → Ty → Set where
  var : Var Γ A → Tm Γ A
  lam : Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

variable t t₁ t₂ u u₁ u₂ : Tm Γ A

-- λf.λz.f ((λx.f x) z)
ex : Tm ε ((∘ ⇒ ∘) ⇒ (∘ ⇒ ∘))
ex = lam (lam (app (var (vs vz))
       (app (lam (app (var (vs (vs vz))) (var vz))) (var vz))))

_-_ : (Γ : Con) → Var Γ A → Con
ε - ()
(Γ , _) - vz = Γ
(Γ , A) - vs x = (Γ - x) , A

wkV : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkV vz y = vs y
wkV (vs x) vz = vz
wkV (vs x) (vs y) = vs (wkV x y)

wkTm : (x : Var Γ A) → Tm (Γ - x) B → Tm Γ B
wkTm x (var v) = var (wkV x v)
wkTm x (lam t) = lam (wkTm (vs x) t)
wkTm x (app t₁ t₂) = app (wkTm x t₁) (wkTm x t₂)

data EqV : Var Γ A → Var Γ B → Set where
  same : EqV x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqV x (wkV x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqV x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
eq (vs x) (vs .x) | same = same
eq (vs x) (vs .(wkV x y)) | diff .x y = diff (vs x) (vs y)

substV : Var Γ B → (x : Var Γ A) → Tm (Γ - x) A → Tm (Γ - x) B
substV v x u with eq x v
substV v .v u | same = u
substV .(wkV v x) .v u | diff v x = var x

substTm : Tm Γ B → (x : Var Γ A) → Tm (Γ - x) A → Tm (Γ - x) B
substTm (var v) x u = substV v x u
substTm (lam t) x u = lam (substTm t (vs x) (wkTm vz u))
substTm (app t₁ t₂) x u = app (substTm t₁ x u) (substTm t₂ x u)

----

data _≡_ : Tm Γ A → Tm Γ A → Set where
  refl : t ≡ t
  sym  : t ≡ u → u ≡ t
  trans : t ≡ t₁ → t₁ ≡ t₂ → t ≡ t₂
  ap-lam : t ≡ u → lam t ≡ lam u
  ap-app : t₁ ≡ t₂ → u₁ ≡ u₂ → app t₁ u₁ ≡ app t₂ u₂
  β : app (lam t) u ≡ substTm t vz u
  η : lam (app (wkTm vz t) (var vz)) ≡ t

data Nf : Con → Ty → Set

data Ne : Con → Ty → Set

data Nf where
  lam : Nf (Γ , A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ ∘ → Nf Γ ∘

data Ne where
  var : Var Γ A → Ne Γ A
  app : Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

-- λf.λz.f (f z)
ex' : Tm ε ((∘ ⇒ ∘) ⇒ (∘ ⇒ ∘))
ex' = lam (lam (app (var (vs vz)) (app (var (vs vz)) (var vz))))

-- λf.λz.f (f z)
exnf : Nf ε ((∘ ⇒ ∘) ⇒ (∘ ⇒ ∘))
exnf = lam (lam (ne (app (var (vs vz)) (ne (app (var (vs vz)) (ne (var vz)))))))

-- λf.λz.f ((λx.f x) z)
wrong : Nf ε ((∘ ⇒ ∘) ⇒ (∘ ⇒ ∘))
wrong = lam (lam (ne (app (var (vs vz)) (ne (app {!!} (ne (var vz)))))))

embNf : Nf Γ A → Tm Γ A
embNe : Ne Γ A → Tm Γ A

embNf (lam nf) = lam (embNf nf)
embNf (ne e) = embNe e

embNe (var v) = var v
embNe (app e nf) = app (embNe e) (embNf nf)

check-ex : embNf exnf ≡ ex'
check-ex = refl

wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B
wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B

wkNf x (lam nf) = lam (wkNf (vs x) nf)
wkNf x (ne e) = ne (wkNe x e)

wkNe x (var v) = var (wkV x v)
wkNe x (app e nf) = app (wkNe x e) (wkNf x nf)

-- Nomarlization function

xyxy xx : Tm ε ((∘ ⇒ ∘) ⇒ (∘ ⇒ ∘))
xyxy = lam (lam (app (var (vs vz)) (var vz)))
xx = lam (var vz)

check : xyxy ≡ xx
check = ap-lam η

-- η-expansion

nvar : Var Γ A → Nf Γ A
nne : Ne Γ A → Nf Γ A

nvar v = nne (var v)

nne {Γ} {∘} x = ne x
nne {Γ} {A ⇒ B} (var v) =
  lam (nne (app (var (vs v)) (nvar vz)))
nne {Γ} {A ⇒ B} (app t u) =
  lam (nne (app (app (wkNe vz t) (wkNf vz u)) (nvar vz)))

-- β-reduction

_[_:=_] : Nf Γ B → (x : Var Γ A)  → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Ne Γ B → (x : Var Γ A) → Nf (Γ - x) A → Ne (Γ - x) B

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

(lam t) [ x := u ] = lam (t [ (vs x) := wkNf vz u ])
ne (var v) [ x := u ] with eq x v
... | same = u
... | diff .x y' = {!!}
ne (app e t) [ x := u ] =
  ne (app (e < x := u >) (t [ x := u ]))

(var v) < x := u > with eq x v
... | same = {!!}
... | diff .x y = {!!}
app x x₃ < x₁ := x₂ > = {!!}

napp (lam t) u = t [ vz := u ]

-- Normalization function
nf : Tm Γ A → Nf Γ A
nf (var v) = nvar v
nf (lam t) = lam (nf t)
nf (app t u) = napp (nf t) (nf u)
