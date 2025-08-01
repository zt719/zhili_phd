-- {-# OPTIONS --cubical-compatible --allow-unsolved-metas #-}

module Cont.HContTry where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Level renaming (zero to lzero; suc to lsuc)

open import Cont.HCont

{- Morphism -}

data NfHom : {Γ : Con} {A : Ty} (t u : Nf Γ A) → Set₁

record NeHom (m n : Ne Γ A) : Set₁

data SpHom : {Γ : Con} {A B : Ty} (t u : Sp Γ A B) → Set₁

data NfHom where
  lam : NfHom t u → NfHom (lam t) (lam u)
  ne  : NeHom spr tql → NfHom (ne spr) (ne tql)

data SpHom where
  ε   : SpHom ts ts
  _,_ : NfHom t u → SpHom ts us → SpHom (t , ts) (u , us)
 
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

HContHom : HCont A → HCont A → Set₁
HContHom = NfHom {∙}

!nf : (t : Nf Γ A) → NfHom t onenf
!nf (lam t) = lam (!nf t)
!nf (ne (S ◃ P ◃ R)) = ne ((λ _ → tt) ◃ (λ x s ()) ◃ λ x s ())

¿nf : (t : Nf Γ A) → NfHom zeronf t
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

<_,_>nf : NfHom t u → NfHom t v → NfHom t (u ×nf v)
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

[_,_]nf : NfHom t v → NfHom u v → NfHom (t ⊎nf u) v
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

{-
napp₁ : (t : HCont (A ⇒ B))
  → HContHom {A} u v
  → HContHom {B} (napp t u) (napp t v)
napp₁ t f = {!!}
-}

data Sub : Con → Con → Set₁ where
  ε   : Sub Γ ∙
  _,_ : Sub Δ Γ → Nf Δ A → Sub Δ (Γ ▹ A)

variable γ δ θ : Sub Δ Γ

wkSub : (x : Var Δ A) → Sub (Δ - x) Γ → Sub Δ Γ
wkSub x ε = ε
wkSub x (γ , t) = wkSub x γ , wkNf x t

_↑ : Sub Δ Γ → Sub (Δ ▹ A) (Γ ▹ A)
γ ↑ = wkSub vz γ , nvar vz

id : Sub Γ Γ
id {∙} = ε
id {Γ ▹ A} = id ↑

subVar : Var Γ A → Sub Δ Γ → Nf Δ A
subVar vz (γ , t) = t
subVar (vs x) (γ , t) = subVar x γ

foldnapp : Nf Γ A → Sp Γ A B → Nf Γ B
foldnapp t ε = t
foldnapp t (u , us) = foldnapp (napp t u) us

_[_]nf : Nf Γ A → Sub Δ Γ → Nf Δ A

-- _[_]ne : Ne Γ A → Sub Δ Γ → Ne Δ A

_[_]sp : Sp Γ A B → Sub Δ Γ → Sp Δ A B

lam t [ γ ]nf = lam (t [ γ ↑ ]nf)
ne (S ◃ P ◃ R) [ γ ]nf = {!!}

ε [ γ ]sp = ε
(t , ts) [ γ ]sp = (t [ γ ]nf) , (ts [ γ ]sp)

_∘_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
ε ∘ γ = ε
(δ , t) ∘ γ = (δ ∘ γ) , (t [ γ ]nf)

lam⁻ : Nf Γ (A ⇒ B) → Nf (Γ ▹ A) B
lam⁻ (lam x) = x

<_> : Nf Γ A → Sub Γ (Γ ▹ A)
< t > = id , t

_$_ : Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B
lam t $ u = t [ < u > ]nf

{- Normalization -}

data Tm : Con → Ty → Set where
  var : Var Γ A → Tm Γ A
  lam : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  one : Tm Γ A
  zero : Tm Γ A
  prod : Tm Γ A → Tm Γ A → Tm Γ A
  copr : Tm Γ A → Tm Γ A → Tm Γ A

nf : Tm Γ A → Nf Γ A
nf (var x) = nvar x
nf (lam x) = lam (nf x)
nf (app t₁ t₂) = napp (nf t₁) (nf t₂)
nf one = onenf
nf zero = zeronf
nf (prod t u) = nf t ×nf nf u
nf (copr t u) = nf t ⊎nf nf u
