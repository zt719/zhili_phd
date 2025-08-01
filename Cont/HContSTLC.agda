module Cont.HContSTLC where

open import Cont.HCont

app : Nf Γ (A ⇒ B) → Nf (Γ ▹ A) B
app (lam x) = x

open import Relation.Binary.PropositionalEquality
  hiding ([_])

β : app (lam t) ≡ t
β = refl

η : lam (app u) ≡ u
η {u = lam u} = refl

data Sub : Ctx → Ctx → Set₁ where
  id : Sub Γ Γ
  _∘_ : Sub Δ Θ → Sub Γ Δ  → Sub Γ Θ
  ε : Sub Γ ∙
  _,_ : Sub Γ Δ → Nf Γ A → Sub Γ (Δ ▹ A)

_[_] : Nf Γ A → Sub Γ Δ → Nf Δ A

wkC : Sub (Γ ▹ A) Γ
wkC = {!!}

_↑ : Sub Γ Δ → Sub (Γ ▹ A) (Δ ▹ A)
σ ↑ = (σ ∘ {!!}) , nvar vz

ξ : {t : Nf (Γ ▹ A) B} {γ : Sub Γ Δ}
  → (lam t) [ γ ] ≡ lam {!!}
ξ = {!!}
