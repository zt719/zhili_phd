module Kripke where

open import Data.String
open import Data.List
open import Data.Unit
open import Data.Empty
open import Data.Product

Prop = Set

variable
  P Q R : Set

variable
  x y : String

infixr 4 _⇒_

data Form : Set where
  Var : String → Form
  _⇒_ : Form → Form → Form

variable
  A B C : Form

Pierce : Form
Pierce = (((Var "P" ⇒ Var "Q") ⇒ Var "P") ⇒ Var "P")

Con = List Form

variable
  Γ Δ Θ : Con

data _⊢_ : Con → Form → Set where
  zero : (A ∷ Γ) ⊢ A
  suc  : Γ ⊢ A → (B ∷ Γ) ⊢ A
  lam  : (A ∷ Γ) ⊢ B → Γ ⊢ (A ⇒ B)
  app  : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B

variable
  d e : Γ ⊢ A

_⊬_ : Con → Form → Set
Γ ⊬ A = Γ ⊢ A → ⊥

record Kripke : Set₁ where
  field
    Worlds : Set
    _⊑_ : Worlds → Worlds → Prop
    refl⊑ : {w : Worlds} → w ⊑ w
    trans⊑ : {w u v : Worlds} → w ⊑ u → u ⊑ v → w ⊑ v
    
    {- Forcing is monotone -}
    _⊩_ : Worlds → String → Prop
    mon⊩ : {w v : Worlds} → v ⊑ w → {x : String} → w ⊩ x → v ⊩ x

  _⊮_ : Worlds → String → Prop
  w ⊮ x = w ⊩ x → ⊥

  _⊩F_ : Worlds → Form → Prop
  w ⊩F Var x = w ⊩ x
  w ⊩F (A ⇒ B) = {v : Worlds} → v ⊑ w → v ⊩F A → v ⊩F B

  _⊮F_ : Worlds → Form → Prop
  w ⊮F A = w ⊩F A → ⊥
  
  _⊩C_ : Worlds → Con → Prop
  w ⊩C [] = ⊤
  w ⊩C (A ∷ Γ) = w ⊩F A × w ⊩C Γ

  {- Γ entails A -}
  _⊨_ : Con → Form → Prop
  Γ ⊨ A = {w : Worlds} → w ⊩C Γ → w ⊩F A

  mon⊩F : {w v : Worlds} → v ⊑ w → w ⊩F A → v ⊩F A
  mon⊩F {Var x} v⊑w v⊩x = mon⊩ v⊑w v⊩x
  mon⊩F {A ⇒ B} u⊑w f v⊑u v⊩A = f (trans⊑ v⊑u u⊑w) v⊩A

  mon⊩C : {w v : Worlds} → v ⊑ w → w ⊩C Γ → v ⊩C Γ
  mon⊩C {[]} v⊑w tt = tt
  mon⊩C {A ∷ Γ} v⊑w (v⊩A , v⊩Γ) = mon⊩F {A = A} v⊑w v⊩A , mon⊩C v⊑w v⊩Γ

  ⟦_⟧ : Γ ⊢ A → Γ ⊨ A
  ⟦ zero ⟧ (p , _) = p
  ⟦ suc d ⟧ (_ , γ) = ⟦ d ⟧ γ
  ⟦ lam d ⟧ wΓ v⊑w vA = ⟦ d ⟧ (vA , mon⊩C v⊑w wΓ)
  ⟦ app d e ⟧ wΓ = ⟦ d ⟧ wΓ refl⊑ (⟦ e ⟧ wΓ)

module Pierce where

  data Worlds : Set where
    w v : Worlds

  data _⊑_ : Worlds → Worlds → Prop where
    w⊑w : w ⊑ w
    v⊑w : v ⊑ w
    v⊑v : v ⊑ v    

  data _⊩_ : Worlds → String → Prop where
    v⊩P : v ⊩ "P"

  refl⊑ : {w : Worlds} → w ⊑ w
  refl⊑ {w} = w⊑w
  refl⊑ {v} = v⊑v

  trans⊑ : {w u v : Worlds} → w ⊑ u → u ⊑ v → w ⊑ v
  trans⊑ w⊑w w⊑w = w⊑w
  trans⊑ v⊑w w⊑w = v⊑w
  trans⊑ v⊑v v⊑w = v⊑w
  trans⊑ v⊑v v⊑v = v⊑v

  mon⊩ : {w v : Worlds} → v ⊑ w → {x : String} → w ⊩ x → v ⊩ x
  mon⊩ v⊑v v⊩x = v⊩x

  PK : Kripke
  PK = record
        { Worlds = Worlds
        ; _⊑_ = _⊑_
        ; refl⊑ = refl⊑
        ; trans⊑ = trans⊑
        ; _⊩_ = _⊩_
        ; mon⊩ = mon⊩
        }

  open Kripke PK using (_⊮_; _⊩F_; _⊮F_; _⊩C_; ⟦_⟧)

  w⊮P : w ⊮ "P"
  w⊮P ()

  w⊮Q : w ⊮ "Q"
  w⊮Q ()

  v⊮Q : v ⊮ "Q"
  v⊮Q ()

  w⊮PQ : w ⊮F (Var "P" ⇒ Var "Q")
  w⊮PQ h = v⊮Q (h v⊑w v⊩P)

  w⊩PQP : w ⊩F ((Var "P" ⇒ Var "Q") ⇒ Var "P")
  w⊩PQP w⊑w f with f v⊑w v⊩P
  ... | ()
  w⊩PQP v⊑w _ = v⊩P

  w⊮Pierce : w ⊮F Pierce
  w⊮Pierce h = w⊮P (h w⊑w w⊩PQP)

  no-Pierce-deriv : [] ⊬ Pierce
  no-Pierce-deriv h = w⊮Pierce (⟦ h ⟧ tt)

module Completeness where

  data _⊢C_ : Con → Con → Set where
    []  : Γ ⊢C []
    _∷_ : Γ ⊢ A → Γ ⊢C Δ → Γ ⊢C (A ∷ Δ)

  idC : Γ ⊢C Γ
  idC {[]} = []
  idC {A ∷ Γ} = zero ∷ wk idC
    where
    wk : Γ ⊢C Δ → (A ∷ Γ) ⊢C Δ
    wk [] = []
    wk (Γ⊢A ∷ Γ⊢Δ) = suc Γ⊢A ∷ wk Γ⊢Δ

  cut : Γ ⊢C Δ → Δ ⊢ A → Γ ⊢ A
  cut [] []⊢A = ∙ []⊢A
    where
    ∙ : [] ⊢ A → Γ ⊢ A
    ∙ {A} {[]} []⊢A = []⊢A
    ∙ {A} {B ∷ Γ} []⊢A = suc (∙ []⊢A)

  cut (Γ⊢A ∷ Γ⊢Δ) zero = Γ⊢A
  cut (Γ⊢A ∷ Γ⊢Δ) (suc Δ⊢A) = cut Γ⊢Δ Δ⊢A
  cut (Γ⊢A ∷ Γ⊢Δ) (lam t) = app (cut Γ⊢Δ (lam (lam t))) Γ⊢A
  cut (Γ⊢A ∷ Γ⊢Δ) (app t u) = app (cut Γ⊢Δ (lam (app t u))) Γ⊢A

  cutC : Γ ⊢C Δ → Δ ⊢C Θ → Γ ⊢C Θ
  cutC Γ⊢Δ [] = []
  cutC Γ⊢Δ (Δ⊢A ∷ Δ⊢Θ) = cut Γ⊢Δ Δ⊢A ∷ cutC Γ⊢Δ Δ⊢Θ

  UM : Kripke
  UM = record
        { Worlds = Con
        ; _⊑_ = _⊢C_
        ; refl⊑ = idC
        ; trans⊑ = cutC
        ; _⊩_ = λ Γ x → Γ ⊢ Var x
        ; mon⊩ = λ Γ⊢Δ Γ⊢x → cut Γ⊢Δ Γ⊢x
        }

  open Kripke UM

{-
  qote : Γ ⊩F A → Γ ⊢ A
  qote x = {!!}
  
  unqote : Γ ⊢ A → Γ ⊩F A
  unqote = {!!}

  completeness : Γ ⊢ A → Γ ⊨ A
  completeness d = {!!}
-}

module Normalisation where

  data _⊢v_ : Con → Form → Set where
    zero : (A ∷ Γ) ⊢v A
    suc  : Γ ⊢v A → (B ∷ Γ) ⊢v A

  data _⊢nf_ : Con → Form → Set

  data _⊢ne_ : Con → Form → Set

  data _⊢sp_,_ : Con → Form → Form → Set

  data _⊢nf_ where
    ne  : Γ ⊢ne (Var x) → Γ ⊢nf (Var x)
    lam : (A ∷ Γ) ⊢nf B → Γ ⊢nf (A ⇒ B) 

  data _⊢ne_ where
    _,_ : Γ ⊢v A → Γ ⊢sp A , B → Γ ⊢ne B

  data _⊢sp_,_ where
    []  : Γ ⊢sp A , A
    _∷_ : Γ ⊢nf A → Γ ⊢sp B , C → Γ ⊢sp (A ⇒ B) , C

  _⊬nf_ : Con → Form → Set
  Γ ⊬nf A = Γ ⊢nf A → ⊥

  data _⊢vC_ : Con → Con → Set where
    []  : Γ ⊢vC []
    _∷_ : Γ ⊢v A → Γ ⊢vC Δ → Γ ⊢vC (A ∷ Δ)

  idvC : Γ ⊢vC Γ
  idvC {[]} = []
  idvC {A ∷ Γ} = zero ∷ wkvC idvC
    where
    wkvC : Γ ⊢vC Δ → (A ∷ Γ) ⊢vC Δ
    wkvC [] = []
    wkvC (Γ⊢A ∷ Γ⊢Δ) = suc Γ⊢A ∷ wkvC Γ⊢Δ

  cutv : Γ ⊢vC Δ → Δ ⊢v A → Γ ⊢v A
  cutv (Γ⊢B ∷ Γ⊢Δ) zero = Γ⊢B
  cutv (Γ⊢B ∷ Γ⊢Δ) (suc Γ⊢A) = cutv Γ⊢Δ Γ⊢A

  cutvC : Γ ⊢vC Δ → Δ ⊢vC Θ → Γ ⊢vC Θ
  cutvC Γ⊢Δ [] = []
  cutvC Γ⊢Δ (Δ⊢A ∷ Δ⊢Θ) = cutv Γ⊢Δ Δ⊢A ∷ cutvC Γ⊢Δ Δ⊢Θ

  cutnf : Γ ⊢vC Δ → Δ ⊢nf A → Γ ⊢nf A
  cutnf [] (ne (() , _))
  cutnf [] (lam A[]⊢B) = lam (cutnf (zero ∷ []) A[]⊢B)
  cutnf (Γ⊢A ∷ Γ⊢Δ) (ne x) = {!!}
  cutnf (Γ⊢A ∷ Γ⊢Δ) (lam BΔ⊢A) = lam {!!}

  NM : Kripke
  NM = record
        { Worlds = Con
        ; _⊑_ = _⊢vC_
        ; refl⊑ = idvC
        ; trans⊑ = cutvC
        ; _⊩_ = λ Γ x → Γ ⊢nf Var x
        ; mon⊩ = λ Γ⊢Δ Δ⊢x → cutnf Γ⊢Δ Δ⊢x
        }

  open Kripke NM

  q : Γ ⊩F A → Γ ⊢nf A
  q = {!!}
