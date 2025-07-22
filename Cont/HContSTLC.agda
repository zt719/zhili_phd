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

data Nfs : Con → Con → Set₁ where
  id : Nfs Γ Γ
  _∘_ : Nfs Δ Θ → Nfs Γ Δ  → Nfs Γ Θ
  ε : Nfs Γ ∙
  _,_ : Nfs Γ Δ → Nf Γ A → Nfs Γ (Δ ▹ A)

_[_] : Nf Γ A → Nfs Γ Δ → Nf Δ A

wkC : Nfs (Γ ▹ A) Γ
wkC = {!!}

_↑ : Nfs Γ Δ → Nfs (Γ ▹ A) (Δ ▹ A)
σ ↑ = (σ ∘ {!!}) , nvar vz

ξ : {t : Nf (Γ ▹ A) B} {γ : Nfs Γ Δ}
  → (lam t) [ γ ] ≡ lam {!!}
ξ = {!!}
