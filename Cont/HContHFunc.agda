module Cont.HContHFunc where

open import Level
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

{- Settings -}

uip : ∀ {ℓ} {A : Set ℓ} {x y : A} →
  (p q : x ≡ y) → p ≡ q
uip refl refl = refl

postulate
  funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
    → {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g
  
{- Types & Contexts & Variables -}

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

variable  A B C : Ty

infixl 5 _▹_
data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

variable  Γ Δ Θ : Con

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

variable t u v : Nf Γ A

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
  
variable ts us : Sp Γ A B

app : Nf Γ (A ⇒ B) → Nf (Γ ▹ A) B
app (lam t) = t

en : Nf Γ * → Ne Γ *
en (ne spr) = spr

{- Variabel Weakening & (Heterogeneous) Equality -}

_-_ : (Γ : Con) → Var Γ A → Con
∙ - ()
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
  P' : Var Γ B → S → Set
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

mutual
  nvar : Var Γ A → Nf Γ A
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

  ne2nf : Ne Γ A → Nf Γ A
  ne2nf {Γ} {*} spr = ne spr
  ne2nf {Γ} {A ⇒ C} (S ◃ P ◃ R) = lam (ne2nf (S ◃ P' ◃ R'))
    where
    P' : Var (Γ ▹ A) B → S → Set
    P' vz s = ⊥
    P' (vs x) s = P x s

    R' : (x : Var (Γ ▹ A) B) (s : S) → P' x s → Sp (Γ ▹ A) B C
    R' vz s ()
    R' (vs x) s p = spSnoc (wkSp vz (R x s p)) (nvar vz)

{- Normalization -}

_[_:=_] : Nf Γ B → (x : Var Γ A) → Nf (Γ - x) A → Nf (Γ - x) B

_<_:=_> : Sp Γ B C → (x : Var Γ A) → Nf (Γ - x) A → Sp (Γ - x) B C

napp : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B

lam t [ x := u ] = lam (t [ vs x := wkNf vz u ])
ne {Γ} (S ◃ P ◃ R) [ x := u ] = ne (S ◃ P' ◃ R')
  where
  P' : Var (Γ - x) A → S → Set
  P' y s = P (wkv x y) s
  
  R' : (y : Var (Γ - x) A) (s : S) → P' y s → Sp (Γ - x) A *
  R' y s p = R (wkv x y) s p < x := u >

ε < x := u > = ε
(t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

napp (lam t) u = t [ vz := u ]

variable I : Set

Πnf : (I : Set) → (I → Nf Γ A) → Nf Γ A
Πnf {Γ} {A ⇒ B} I ts = lam (Πnf I (λ i → app (ts i)))
Πnf {Γ} {*} I ts = ne (S ◃ P ◃ R)
  where
  S : Set
  S = (i : I) → en (ts i) .Ne.S

  P : Var Γ A → S → Set
  P x f = Σ[ i ∈ I ] en (ts i) .Ne.P x (f i)

  R : (x : Var Γ A) (s : S) → P x s → Sp Γ A *
  R x f (i , p) = en (ts i) .Ne.R x (f i) p

Σnf : (I : Set) → (I → Nf Γ A) → Nf Γ A
Σnf {Γ} {A ⇒ B} I ts = lam (Σnf I (λ i → app (ts i)))
Σnf {Γ} {*} I ts = ne (S ◃ P ◃ R)
  where
  S : Set
  S = Σ[ i ∈ I ] en (ts i) .Ne.S

  P : Var Γ A → S → Set
  P x (i , s) = en (ts i) .Ne.P x s

  R : (x : Var Γ A) (s : S) → P x s → Sp Γ A *
  R x (i , s) p = en (ts i) .Ne.R x s p

infix 2 Σnf-syntax
Σnf-syntax : (I : Set) → (I → Nf Γ A) → Nf Γ A
Σnf-syntax = Πnf
syntax Σnf-syntax A (λ x → B) = Σnf[ x ∈ A ] B

infix 2 Πnf-syntax
Πnf-syntax : (I : Set) → (I → Nf Γ A) → Nf Γ A
Πnf-syntax = Πnf
syntax Πnf-syntax A (λ x → B) = Πnf[ x ∈ A ] B

{- Normal From Homomorphisms -}

data NfHom : Nf Γ A → Nf Γ A → Set₁

record NeHom {Γ} {B} (spr tql : Ne Γ B) : Set₁

data SpHom : Sp Γ A B → Sp Γ A B → Set₁

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

{-- Semantics --}

record Cat (Obj : Set₁) : Set₂ where
  infixr 9 _∘_
  field
    Hom : Obj → Obj → Set₁
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    ass : ∀ {W X Y Z} (f : Hom X W) (g : Hom Y X) (h : Hom Z Y)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

record Func {A B : Set₁} (ℂ : Cat A) (𝔻 : Cat B) (F : A → B) : Set₁ where
  open Cat
  field
    F₁ : ∀ {X Y} → Hom ℂ X Y → Hom 𝔻 (F X) (F Y)
    F-id : ∀ {X} → F₁ {X} (ℂ .id) ≡ 𝔻 .id
    F-∘ : ∀ {X Y Z} (f : Hom ℂ Y Z) (g : Hom ℂ X Y)
          → F₁ (ℂ ._∘_ f g ) ≡ 𝔻 ._∘_ (F₁ f) (F₁ g)

record Nat {A B : Set₁} (ℂ : Cat A) (𝔻 : Cat B)
  (F G : A → B) (FF : Func ℂ 𝔻 F) (GG : Func ℂ 𝔻 G) : Set₁ where
  open Cat
  open Func
  field
    η : ∀ X → Hom 𝔻 (F X) (G X)
    nat : ∀ {X Y} (f : Hom ℂ X Y)
      → 𝔻 ._∘_ (GG .F₁ f) (η X) ≡ 𝔻 ._∘_ (η Y) (FF .F₁ f)

postulate
  NatExt : {A B : Set₁} {ℂ : Cat A} {𝔻 : Cat B} {F G : A → B}
      → {FF : Func ℂ 𝔻 F} {GG : Func ℂ 𝔻 G}
      → {α β : Nat ℂ 𝔻 F G FF GG}
      → α .Nat.η ≡ β .Nat.η → α ≡ β
{-      
NatExt {A} {B} {ℂ} {𝔻} {F} {G} {FF} {GG}
  {record { η = α ; nat = nat-α }}
  {record { η = β ; nat = nat-β }}
  η≡ = dcong₂ {A = (X : A) → Cat.Hom 𝔻 (F X) (G X)}
    {B = λ η → {X Y : A} (f : Cat.Hom ℂ X Y)
      → 𝔻 .Cat._∘_ (GG .Func.F₁ f) (η X) ≡ 𝔻 .Cat._∘_ (η Y) (FF .Func.F₁ f)}
    (λ η nat → record { η = η ; nat = nat }) η≡ {!!}
-}

⟦_⟧t : Ty → Set₁
⟦ * ⟧t = Set
⟦ A ⇒ B ⟧t = ⟦ A ⟧t → ⟦ B ⟧t

⟦_⟧c : Con → Set₁
⟦ ∙ ⟧c = Lift (suc zero) ⊤
⟦ Γ ▹ A ⟧c = ⟦ Γ ⟧c × ⟦ A ⟧t

⟦_⟧v : Var Γ A → ⟦ Γ ⟧c → ⟦ A ⟧t
⟦ vz ⟧v (as , a) = a
⟦ vs x ⟧v (as , a) = ⟦ x ⟧v as

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧c → ⟦ A ⟧t

⟦_⟧ne : Ne Γ * → ⟦ Γ ⟧c → Set

⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧c → ⟦ A ⟧t → ⟦ B ⟧t

⟦ lam t ⟧nf as a = ⟦ t ⟧nf (as , a)
⟦ ne spr ⟧nf as = ⟦ spr ⟧ne as

⟦_⟧ne {Γ} (S ◃ P ◃ R) as =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P x s)
  → ⟦ R x s p ⟧sp as (⟦ x ⟧v as))

⟦ ε ⟧sp as a = a
⟦ t , ts ⟧sp as f = ⟦ ts ⟧sp as (f (⟦ t ⟧nf as))

{- Hereditary Functor and Category -}

⟦_⟧Func : (A : Ty) → ⟦ A ⟧t → Set₁

HFunc : (A : Ty) → Set₁
HFunc A = Σ ⟦ A ⟧t ⟦ A ⟧Func

⟦_⟧Cat : (A : Ty) → Cat (HFunc A)

⟦ * ⟧Func X = Lift (suc zero) ⊤
⟦ A ⇒ B ⟧Func H =
  Σ[ HH ∈ ((F : ⟦ A ⟧t) → ⟦ A ⟧Func F → ⟦ B ⟧Func (H F)) ]
  Func ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (F , FF) → H F , HH F FF)

⟦ * ⟧Cat = record
  { Hom = λ (X , lift tt) (Y , lift tt) → Lift (suc zero) (X → Y)
  ; id = lift (λ x → x)
  ; _∘_ = λ{ (lift f) (lift g) → lift (λ x → f (g x)) }
  ; idl = λ f → refl
  ; idr = λ f → refl
  ; ass = λ f g h → refl
  }
⟦ A ⇒ B ⟧Cat = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧Cat ⟦ B ⟧Cat (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG
  ; id = record
    { η = λ X → id
    ; nat = λ f → trans (idr _) (sym (idl _))
    }
  ; _∘_ = λ α β → record
    { η = λ X → α .η X ∘ β .η X
    ; nat = λ f → trans (sym (ass _ _ _)) (trans (cong (_∘ _) (α .nat f))
      (trans (ass _ _ _) (trans (cong (_ ∘_) (β .nat f)) (sym (ass _ _ _)))))
    }
  ; idl = λ α → NatExt (funExt λ X → idl (α .η X))
  ; idr = λ α → NatExt (funExt λ X → idr (α .η X))
  ; ass = λ α β γ → NatExt (funExt λ X → ass (α .η X) (β .η X) (γ .η X))
  }
  where
    open Cat ⟦ B ⟧Cat
    open Nat

HCont : Ty → Set₁
HCont A = Nf ∙ A

⟦_⟧ : HCont A → ⟦ A ⟧t
⟦ x ⟧ = ⟦ x ⟧nf (lift tt)

⟦_⟧nf₁ : (t : Nf Γ A) (γ : ⟦ Γ ⟧c) → ⟦ A ⟧Func (⟦ t ⟧nf γ)

open Cat

F₁ : {Γ : Con} {A B : Ty} {(X , XX) (Y , YY) : HFunc A}
  (t : Nf (Γ ▹ A) B) (γ : ⟦ Γ ⟧c)
  → ⟦ A ⟧Cat .Hom (X , XX) (Y , YY)
  → ⟦ B ⟧Cat .Hom (⟦ t ⟧nf (γ , X) , ⟦ t ⟧nf₁ (γ , X)) (⟦ t ⟧nf (γ , Y) , ⟦ t ⟧nf₁ (γ , Y))

F-id : {Γ : Con} {A B : Ty} {X : HFunc A}
  → (t : Nf (Γ ▹ A) B) (γ : ⟦ Γ ⟧c)
  → F₁ {Γ} {A} {B} {X} t γ (⟦ A ⟧Cat .id) ≡ ⟦ B ⟧Cat .id

F-∘ : {Γ : Con} {A B : Ty} {X Y Z : HFunc A} 
  → (t : Nf (Γ ▹ A) B) (γ : ⟦ Γ ⟧c)
  → (f : ⟦ A ⟧Cat .Hom Y Z) (g : ⟦ A ⟧Cat .Hom X Y)
  → F₁ t γ (⟦ A ⟧Cat ._∘_ f g) ≡ ⟦ B ⟧Cat ._∘_ (F₁ t γ f) (F₁ t γ g)


⟦ ne x ⟧nf₁ as = lift tt
⟦ lam t ⟧nf₁ γ
  = (λ a afunc → ⟦ t ⟧nf₁ (γ , a)) , record
    { F₁ = F₁ t γ
    ; F-id = F-id t γ
    ; F-∘ = F-∘ t γ
    }

v-sub : {Γ : Con} {A : Ty} (x : Var (Γ ▹ A) *)
  (γ : ⟦ Γ ⟧c) ((a , a₁) (a' , a₁') : HFunc A)
  → ⟦ A ⟧Cat .Hom (a , a₁) (a' , a₁')
  → ⟦ x ⟧v (γ , a) → ⟦ x ⟧v (γ , a')
v-sub {Γ} {*} vz γ (a , a₁) (a' , a₁') (lift f) o = f o
v-sub {Γ} {*} (vs x) γ (a , a₁) (a' , a₁') (lift f) o = o
v-sub {Γ} {A ⇒ B} (vs x) γ (a , a₁) (a' , a₁') _ o = o

aux-sp : {Γ : Con} {A B : Ty} {γ : ⟦ Γ ⟧c}
  (u : Nf (Γ ▹ A) B) (ts : Sp (Γ ▹ A) B *)
  ((a , a₁) (a' , a₁') : HFunc A)  
  → ⟦ A ⟧Cat .Hom (a , a₁) (a' , a₁')
  → ⟦ ts ⟧sp (γ , a) (⟦ u ⟧nf (γ , a))
  → ⟦ ts ⟧sp (γ , a') (⟦ u ⟧nf (γ , a'))
aux-sp {Γ} {A} {*} {γ} u ε (a , a₁) (a' , a₁') hom o = {!!}
aux-sp {Γ} {A} {B ⇒ C} {γ} u (t , ts) (a , a₁) (a' , a₁') hom o =
  aux-sp {Γ} {A} {C} {γ} (napp u t) {!!}
  (a , a₁) (a' , a₁') hom {!!}

aux-nf : {Γ : Con} {A B : Ty} {γ : ⟦ Γ ⟧c}
  (x : Var (Γ ▹ A) B) (t : Nf (Γ ▹ A) *)
  ((a , a₁) (a' , a₁') : HFunc A)  
  → ⟦ A ⟧Cat .Hom (a , a₁) (a' , a₁')
  → ⟦ t ⟧nf (γ , a) → ⟦ t ⟧nf (γ , a')

aux-ne : {Γ : Con} {A B : Ty} {γ : ⟦ Γ ⟧c}
  (x : Var (Γ ▹ A) B) (t : Ne (Γ ▹ A) *)
  ((a , a₁) (a' , a₁') : HFunc A)  
  → ⟦ A ⟧Cat .Hom (a , a₁) (a' , a₁')
  → ⟦ t ⟧ne (γ , a) → ⟦ t ⟧ne (γ , a')

aux-nf {Γ} {A} {B} {γ} x (ne spr) (a , a₁) (a' , a₁') hom o
  = aux-ne x spr (a , a₁) (a' , a₁') hom o

aux-ne {Γ} {A} {B} {γ} _ (S ◃ P ◃ R) (a , a₁) (a' , a₁') hom (s , f)
  = s , λ x p → {!!}

F₁ {Γ} {A} {*} {X , XX} {Y , YY} (ne (S ◃ P ◃ R)) γ hom =
  lift λ{ (s , f) → s , λ x p → {!!} }
F₁ {Γ} {A} {B ⇒ C} {X , XX} {Y , YY} (lam t) γ hom = record
  { η = λ{ (Z , ZZ) → {!!}  }
  ; nat = {!!}
  }

F-id {Γ} {A} {*} {X} t γ = {!!}
F-id {Γ} {A} {B ⇒ C} {X} t γ = {!!}

F-∘ = {!!}

⟦_⟧Nf : Nf Γ A → ⟦ Γ ⟧c → HFunc A
⟦ t ⟧Nf γ = ⟦ t ⟧nf γ , ⟦ t ⟧nf₁ γ

⟦_⟧₁ : (H : HCont A) → ⟦ A ⟧Func ⟦ H ⟧
⟦ H ⟧₁ = ⟦ H ⟧nf₁ (lift tt)

⟦_⟧Full : HCont A → HFunc A
⟦ H ⟧Full = ⟦ H ⟧Nf (lift tt)
