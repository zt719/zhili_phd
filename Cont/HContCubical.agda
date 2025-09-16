{-# OPTIONS --cubical --guardedness #-}

module Cont.HContCubical where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
  
{- Types & Contexts & Variables -}

infixr 20 _⇒_
data Ty : Type where
  * : Ty
  _⇒_ : Ty → Ty → Ty
  TyIsSet : isSet Ty

variable  A B C : Ty

infixl 5 _▹_
data Con : Type where
  ∙   : Con
  _▹_ : Con → Ty → Con

variable  Γ Δ Θ : Con

ConIsSet : isSet Con
ConIsSet ∙ ∙ p q = {!!}
ConIsSet ∙ (y ▹ x) p q = {!!}
ConIsSet (x ▹ x₁) ∙ p q = {!!}
ConIsSet (x ▹ x₁) (y ▹ x₂) p q = {!!}

data Var : Con → Ty → Type where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y : Var Γ A

{- Normal Forms -}

infixr 4 _,_

data Nf : Con → Ty → Type₁

record Ne (Γ : Con) (B : Ty) : Type₁

data Sp : Con → Ty → Ty → Type₁

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ * → Nf Γ *
  NfIsSet : ∀ {Γ A} → isSet (Nf Γ A)

variable t u w : Nf Γ A

record Ne Γ B where
  constructor _◃_◃_
  inductive
  field
    S : Type
    P : Var Γ A → S → Type
    R : (x : Var Γ A) (s : S) → P x s → Sp Γ A B
    SIsSet : isSet S
    PIsSet : {A : Ty} {x : Var Γ A} {s : S} → isSet (P x s)

variable spr tql : Ne Γ A

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  SpIsSet : ∀ {Γ A B} → isSet (Sp Γ A B)
  
variable ts us ws : Sp Γ A B


{-

ap : Nf Γ (A ⇒ B) → Nf (Γ ▹ A) B
ap {Γ} {A} {B} x = {!!}

en : Nf Γ * → Ne Γ *
en (ne spr) = spr

{- Variable Weakening & (Heterogeneous) Equality -}

_-_ : (Γ : Con) → Var Γ A → Con
∙ - ()
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - (vs x) = (Γ - x) ▹ A

wkv : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

data EqVar : Var Γ A → Var Γ B → Type where
  same : EqVar x x
  diff : (x : Var Γ A) (y : Var (Γ - x) B) → EqVar x (wkv x y)

eq : (x : Var Γ A) (y : Var Γ B) → EqVar x y
eq vz vz = same
eq vz (vs y) = diff vz y
eq (vs x) vz = diff (vs x) vz
eq (vs x) (vs y) with eq x y
eq (vs x) (vs .x)            | same = same
eq (vs x) (vs .(wkv x y')) | diff .x y' = diff (vs x) (vs y')

{- Normal Forms Weakening -}
wkNf : (x : Var Γ A) → Nf (Γ - x) B → Nf Γ B

wkNe : (x : Var Γ A) → Ne (Γ - x) B → Ne Γ B

wkSp : (x : Var Γ A) → Sp (Γ - x) B C → Sp Γ B C

wkNf x (lam t) = lam (wkNf (vs x) t)
wkNf x (ne spr) = ne (wkNe x spr)

wkNe {Γ} {A} {C} x (S ◃ P ◃ R) = S ◃ P' ◃ R'
  where
  P' : Var Γ B → S → Type
  P' y  s with eq x y
  P' .x s | same = ⊥
  P' y  s | diff .x y' = P y' s

  R' : (y : Var Γ B) (s : S) → P' y s → Sp Γ B C
  R' y s p with eq x y
  R' y s p | diff .x y' = wkSp x (R y' s p)

wkSp x ε = ε
wkSp x (t , ts) = wkNf x t , wkSp x ts

{- η-expansion -}

spSnoc : Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
spSnoc ε u = u , ε
spSnoc (t , ts) u = t , spSnoc ts u

nvar : Var Γ A → Nf Γ A

ne2nf : Ne Γ A → Nf Γ A

nvar {Γ} {B} x = ne2nf (S ◃ P ◃ R)
  where
  S : Type
  S = ⊤

  P : Var Γ A → S → Type
  P y  tt with eq x y
  P .x tt | same = ⊤
  P y  tt | diff .x y' = ⊥

  R : (y : Var Γ A) (s : S) → P y s → Sp Γ A B
  R y tt p with eq x y
  R .x tt p | same = ε
  R y tt () | diff .x y'

ne2nf {Γ} {*} spr = ne spr
ne2nf {Γ} {A ⇒ C} (S ◃ P ◃ R) = lam (ne2nf (S ◃ P' ◃ R'))
  where
  P' : Var (Γ ▹ A) B → S → Type
  P' vz s = ⊥
  P' (vs x) s = P x s

  R' : (x : Var (Γ ▹ A) B) (s : S) → P' x s → Sp (Γ ▹ A) B C
  R' vz s ()
  R' (vs x) s p = spSnoc (wkSp vz (R x s p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

_◇_ : Nf Γ A → Sp Γ A B → Nf Γ B

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

lam t [ x := u ] = lam (t [ vs x := wkNf vz u ])
ne {Γ} (S ◃ P ◃ R) [ x := u ] = ne (S ◃ P' ◃ R')
  where
  P' : Var (Γ - x) A → S → Type
  P' y s = P (wkv x y) s
  
  R' : (y : Var (Γ - x) A) (s : S) → P' y s → Sp (Γ - x) A *
  R' y s p = R (wkv x y) s p < x := u >

ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

t ◇ ε = t
t ◇ (u , us) = napp t u ◇ us

napp (lam t) u = t [ vz := u ]

{-
{- Algebraic Structures -}

⊤nf : Nf Γ A
⊤nf {Γ} {*} = ne (⊤ ◃ (λ{ x tt → ⊥ }) ◃ λ{ x tt () })
⊤nf {Γ} {A ⇒ B} = lam ⊤nf

⊥nf : Nf Γ A
⊥nf {Γ} {*} = ne (⊥ ◃ (λ x ()) ◃ (λ x ()))
⊥nf {Γ} {A ⇒ B} = lam ⊥nf

_×nf_ : Nf Γ A → Nf Γ A → Nf Γ A
lam t ×nf lam u = lam (t ×nf u)
_×nf_ {Γ} {B} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (S' ◃ P' ◃ R')
  where
  S' : Type
  S' = S × T

  P' : Var Γ A → S' → Type
  P' x (s , t) = P x s ⊎ Q x t

  R' : (x : Var Γ A) (s : S') → P' x s → Sp Γ A B
  R' x (s , t) (inj₁ p) = R x s p
  R' x (s , t) (inj₂ q) = L x t q

_⊎nf_ : Nf Γ A → Nf Γ A → Nf Γ A
lam t ⊎nf lam u = lam (t ⊎nf u)
_⊎nf_ {Γ} {B} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (S' ◃ P' ◃ R')
  where
  S' : Type
  S' = S ⊎ T

  P' : Var Γ A → S' → Type
  P' x (inj₁ s) = P x s
  P' x (inj₂ t) = Q x t

  R' : (x : Var Γ A) (s : S') → P' x s → Sp Γ A B
  R' x (inj₁ s) p = R x s p
  R' x (inj₂ t) q = L x t q

Πnf : (I : Type) → (I → Nf Γ A) → Nf Γ A
Πnf {Γ} {A ⇒ B} I ts = lam (Πnf I (λ i → ap (ts i)))
Πnf {Γ} {*} I ts = ne (S ◃ P ◃ R)
  where
  S : Type
  S = (i : I) → en (ts i) .Ne.S

  P : Var Γ A → S → Type
  P x f = Σ[ i ∈ I ] en (ts i) .Ne.P x (f i)

  R : (x : Var Γ A) (s : S) → P x s → Sp Γ A *
  R x f (i , p) = en (ts i) .Ne.R x (f i) p

Σnf : (I : Type) → (I → Nf Γ A) → Nf Γ A
Σnf {Γ} {A ⇒ B} I ts = lam (Σnf I (λ i → ap (ts i)))
Σnf {Γ} {*} I ts = ne (S ◃ P ◃ R)
  where
  S : Type
  S = Σ[ i ∈ I ] en (ts i) .Ne.S

  P : Var Γ A → S → Type
  P x (i , s) = en (ts i) .Ne.P x s

  R : (x : Var Γ A) (s : S) → P x s → Sp Γ A *
  R x (i , s) p = en (ts i) .Ne.R x s p

infix 2 Σnf-syntax
Σnf-syntax : (I : Type) → (I → Nf Γ A) → Nf Γ A
Σnf-syntax = Πnf
syntax Σnf-syntax A (λ x → B) = Σnf[ x ∈ A ] B

infix 2 Πnf-syntax
Πnf-syntax : (I : Type) → (I → Nf Γ A) → Nf Γ A
Πnf-syntax = Πnf
syntax Πnf-syntax A (λ x → B) = Πnf[ x ∈ A ] B

{- Morphisms -}

data NfHom : Nf Γ A → Nf Γ A → Type₁

record NeHom {Γ} {B} (spr tql : Ne Γ B) : Type₁

data SpHom : Sp Γ A B → Sp Γ A B → Type₁

data NfHom where
  lam : NfHom t u → NfHom (lam t) (lam u)
  ne  : NeHom spr tql → NfHom (ne spr) (ne tql)

record NeHom {Γ} {B} spr tql where
  constructor _◃_◃_
  inductive
  open Ne spr
  open Ne tql renaming (S to T; P to Q; R to L)
  field
    f : S → T
    g : (x : Var Γ A) (s : S) → Q x (f s) → P x s
    h : (x : Var Γ A) (s : S) (q : Q x (f s))
      → SpHom (R x s (g x s q)) (L x (f s) q)
       
data SpHom where
  ε   : SpHom ts ts
  _,_ : NfHom t u → SpHom ts us → SpHom (t , ts) (u , us)

idNfHom : NfHom t t
idNfHom {t = ne spr} = ne (id ◃ (λ x s → id) ◃ λ x s q → ε)
idNfHom {t = lam t} = lam (idNfHom {t = t})

_∘nfHom_ : NfHom u w → NfHom t u → NfHom t w
_∘spHom_ : SpHom us ws → SpHom ts us → SpHom ts ws

lam f ∘nfHom lam g = lam (f ∘nfHom g)
ne (f ◃ g ◃ h) ∘nfHom ne (f' ◃ g' ◃ h') = ne (
  (f ∘ f')
  ◃ (λ x s → g' x s ∘ g x (f' s))
  ◃ λ x s q → (h x (f' s) q) ∘spHom h' x s (g x (f' s) q)
  )

ε ∘spHom ε = ε
ε ∘spHom (g , gs) = g , gs
(f , fs) ∘spHom ε = f , fs
(f , fs) ∘spHom (g , gs) = (f ∘nfHom g) , (fs ∘spHom gs)


!nf : (t : Nf Γ A) → NfHom t ⊤nf
!nf (lam t) = lam (!nf t)
!nf (ne (S ◃ P ◃ R)) = ne ((λ _ → tt) ◃ (λ x s ()) ◃ λ x s ())

¿nf : (t : Nf Γ A) → NfHom ⊥nf t
¿nf (lam t) = lam (¿nf t)
¿nf (ne (S ◃ P ◃ R)) = ne ((λ ()) ◃ (λ x ()) ◃ λ x ())

π₁nf : (t u : Nf Γ A) → NfHom (t ×nf u) t
π₁nf (lam t) (lam u) = lam (π₁nf t u)
π₁nf {Γ} {B} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (f ◃ g ◃ h)
  where
  f : S × T → S
  f (s , t) = s

  g : (x : Var Γ A) (st : S × T) → P x (f st) → P x (st .proj₁) ⊎ Q x (st .proj₂)
  g x (s , t) p = inj₁ p

  h : (x : Var Γ A) (st : S × T) (q : P x (f st)) → SpHom (R x (f st) q) (R x (f st) q)
  h x (s , t) q = ε

i₁nf : (t u : Nf Γ A) → NfHom t (t ⊎nf u)
i₁nf (lam t) (lam u) = lam (i₁nf t u)
i₁nf {Γ} (ne (S ◃ P ◃ R)) (ne (T ◃ Q ◃ L)) = ne (f ◃ g ◃ h)
  where
  f : S → S ⊎ T
  f s = inj₁ s

  g : (x : Var Γ A) (s : S) → P x s → P x s
  g x s p = p

  h : (x : Var Γ A) (s : S) (q : P x s) → SpHom (R x s (g x s q)) (R x s q)
  h x s q = ε

<_,_>nf : NfHom t u → NfHom t w → NfHom t (u ×nf w)
< lam tu , lam tv >nf = lam < tu , tv >nf
<_,_>nf {Γ} {B} (ne (f₁ ◃ g₁ ◃ h₁)) (ne (f₂ ◃ g₂ ◃ h₂)) = ne (ff ◃ gg ◃ hh)
  where
  ff : _
  ff = < f₁ , f₂ >

  gg : (x : Var Γ A) (s : _) → _
  gg x s (inj₁ q₁) = g₁ x s q₁
  gg x s (inj₂ q₂) = g₂ x s q₂

  hh : (x : Var Γ A) (s : _) (q : _) → _
  hh x s (inj₁ q₁) = h₁ x s q₁
  hh x s (inj₂ q₂) = h₂ x s q₂

[_,_]nf : NfHom t w → NfHom u w → NfHom (t ⊎nf u) w
[ lam tv , lam uv ]nf = lam [ tv , uv ]nf
[_,_]nf {Γ} {B} (ne (f₁ ◃ g₁ ◃ h₁)) (ne (f₂ ◃ g₂ ◃ h₂)) = ne (ff ◃ gg ◃ hh)
  where
  ff : _
  ff = [ f₁ , f₂ ]

  gg : (x : Var Γ A) (s : _) → _
  gg x (inj₁ s₁) q₁ = g₁ x s₁ q₁
  gg x (inj₂ s₂) q₂ = g₂ x s₂ q₂

  hh : (x : Var Γ A) (s : _) (q : _) → _
  hh x (inj₁ s₁) q₁ = h₁ x s₁ q₁
  hh x (inj₂ s₂) q₂ = h₂ x s₂ q₂

{- Simply Typed Categories with Families -}

data Nfs : Con → Con → Type₁ where
  ε   : Nfs Γ ∙
  _,_ : Nfs Δ Γ → Nf Δ A → Nfs Δ (Γ ▹ A)

variable γ δ θ : Nfs Δ Γ

wkNfs : (x : Var Δ A) → Nfs (Δ - x) Γ → Nfs Δ Γ
wkNfs x ε = ε
wkNfs x (γ , t) = wkNfs x γ , wkNf x t

_↑ : Nfs Δ Γ → Nfs (Δ ▹ A) (Γ ▹ A)
γ ↑ = wkNfs vz γ , nvar vz

subVar : Var Γ A → Nfs Δ Γ → Nf Δ A
subVar vz (γ , t) = t
subVar (vs x) (γ , t) = subVar x γ

appSp : Nf Γ A → Sp Γ A B → Nf Γ B
appSp t ε = t
appSp t (u , us) = appSp (napp t u) us

_[_]nf : Nf Γ A → Nfs Δ Γ → Nf Δ A

_[_]sp : Sp Γ A B → Nfs Δ Γ → Sp Δ A B

lam t [ γ ]nf = lam (t [ γ ↑ ]nf)
ne (S ◃ P ◃ R) [ γ ]nf = Σnf[ s ∈ S ]
  Πnf[ A ∈ Ty ] Πnf[ x ∈ Var _ A ] Πnf[ p ∈ P x s ]
  appSp (subVar x γ) (R x s p [ γ ]sp)

ε [ γ ]sp = ε
(t , ts) [ γ ]sp = (t [ γ ]nf) , (ts [ γ ]sp)

idNfs : Nfs Γ Γ
idNfs {∙} = ε
idNfs {Γ ▹ A} = idNfs ↑

_∘nfs_ : Nfs Δ Γ → Nfs Θ Δ → Nfs Θ Γ
ε ∘nfs γ = ε
(δ , t) ∘nfs γ = (δ ∘nfs γ) , (t [ γ ]nf)

π₁ : Nfs Δ (Γ ▹ A) → Nfs Δ Γ
π₁ (γ , t) = γ

π₂ : Nfs Δ (Γ ▹ A) → Nf Δ A
π₂ (γ , t) = t

wk : Nfs (Γ ▹ A) Γ
wk = π₁ idNfs

nvz : Nf (Γ ▹ A) A
nvz = π₂ idNfs

nvs : Nf Γ A → Nf (Γ ▹ B) A
nvs t = t [ wk ]nf

<_> : Nf Γ A → Nfs Γ (Γ ▹ A)
< t > = idNfs , t

π₁β : π₁ (γ , t) ≡ γ
π₁β = refl

π₂β : π₂ (γ , t) ≡ t
π₂β = refl

πη : (π₁ γ , π₂ γ) ≡ γ
πη {γ = γ , t} = refl

,∘ : (γ , t) ∘nfs δ ≡ (γ ∘nfs δ , t [ δ ]nf)
,∘ = refl

{-
[id]nf : t [ id ]nf ≡ t
[id]nf {t = lam t} = cong lam [id]nf
[id]nf {Γ} {t = ne (S ◃ P ◃ R)} = {!!}

↑dis : _↑ {Δ} {Γ} {A} (δ ∘ γ) ≡ ((δ ↑) ∘ (γ ↑))
↑dis {Δ} {Γ} {A} {δ = ε} {γ = γ} = {!!}
↑dis {δ = δ , x} {γ = γ} = {!!}

[∘]nf : t [ δ ∘ γ ]nf ≡ t [ δ ]nf [ γ ]nf
[∘]nf {t = lam t} = cong lam (trans {!!} {!!})
[∘]nf {t = ne x} = {!!}

nvz[] : nvz [ (γ , t) ]nf ≡ t
nvz[] {γ = γ} {t = t} = {!!}

nvs[] : nvs t [ (γ , u) ]nf ≡ t [ γ ]nf
nvs[] = {!!}

idl : id ∘ γ ≡ γ
idl {γ = ε} = refl
idl {γ = γ , t} = cong₂ _,_ {!!} nvz[]

idr : γ ∘ id ≡ γ
idr {γ = ε} = refl
idr {γ = γ , t} = cong₂ _,_ idr [id]nf

ass : (θ ∘ δ) ∘ γ ≡ θ ∘ (δ ∘ γ)
ass {θ = ε} = refl
ass {θ = θ , t} = cong₂ _,_ ass (sym ([∘]nf {t = t}))

⇒β : app (lam t) ≡ t
⇒β = refl

⇒η : lam (app t) ≡ t
⇒η {t = lam t} = refl

↑≡ : γ ↑ ≡ (γ ∘ π₁ {A = A} id , π₂ id)
↑≡ {γ = ε} = refl
↑≡ {γ = γ , t} = cong₂ _,_ (cong₂ _,_ {!!} {!!}) refl

lam[]nf : lam t [ γ ]nf ≡ lam (t [ γ ↑ ]nf)
lam[]nf = refl

app[]nf : app (t [ γ ]nf) ≡ app t [ γ ↑ ]nf
app[]nf {t = lam t} = refl
-}

{-- Semantics --}

{- Normal Form Functors -}

⟦_⟧t : Ty → Type₁
⟦ * ⟧t = Type
⟦ A ⇒ B ⟧t = ⟦ A ⟧t → ⟦ B ⟧t

⟦_⟧c : Con → Type₁
⟦ ∙ ⟧c = Lift (lsuc lzero) ⊤
⟦ Γ ▹ A ⟧c = ⟦ Γ ⟧c × ⟦ A ⟧t

⟦_⟧v : Var Γ A → ⟦ Γ ⟧c → ⟦ A ⟧t
⟦ vz ⟧v (as , a) = a
⟦ vs x ⟧v (as , a) = ⟦ x ⟧v as

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧c → ⟦ A ⟧t

⟦_⟧ne : Ne Γ * → ⟦ Γ ⟧c → Type

⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧c → ⟦ A ⟧t → ⟦ B ⟧t

⟦ lam t ⟧nf as a = ⟦ t ⟧nf (as , a)
⟦ ne spr ⟧nf as = ⟦ spr ⟧ne as

⟦_⟧ne {Γ} (S ◃ P ◃ R) as =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P x s)
  → ⟦ R x s p ⟧sp as (⟦ x ⟧v as))

⟦ ε ⟧sp as a = a
⟦ t , ts ⟧sp as f = ⟦ ts ⟧sp as (f (⟦ t ⟧nf as))

data Tm : Con → Ty → Type₁ where
  var : Var Γ A → Tm Γ A
  lam : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  Πtm : (I : Type) → (I → Tm Γ A) → Tm Γ A
  Σtm : (I : Type) → (I → Tm Γ A) → Tm Γ A

nf : Tm Γ A → Nf Γ A
nf (var x) = nvar x
nf (lam t) = lam (nf t)
nf (app t u) = napp (nf t) (nf u)
nf (Πtm I t⃗) = Πnf I (nf ∘ t⃗)
nf (Σtm I t⃗) = Σnf I (nf ∘ t⃗)
-}
-}
