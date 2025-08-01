{-# OPTIONS --cubical --guardedness #-}

module Cont.HContTryProof where

open import Cont.HCont
open import Cont.HContTry
open import Cubical.Foundations.Prelude

⇒β  : app (lam t) ≡ t
⇒β = refl

⇒η  : lam (app t) ≡ t
⇒η {t = lam t} = refl

[id] : t [ id ] ≡ t
[id] = {!!}

[∘] : t [ γ ∘ δ ] ≡ t [ γ ] [ δ ]
[∘] = {!!}

vz-[] : nvar vz [ γ , t ] ≡ t
vz-[] {γ = γ} {t = t} =
  nvar vz [ γ , t ] ≡⟨ {!!} ⟩
  {!!} ≡⟨ {!!} ⟩ {!!}

idl  : id ∘ γ ≡ γ
idl {γ = ε} = refl
idl {γ = γ , t} i = {!!} , vz-[] {γ = γ} {t = t} i

idr  : γ ∘ id ≡ γ
idr = {!!}


ass  : (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
ass {γ = ε} {δ = δ} {θ = θ} = refl
ass {γ = γ , t} {δ = δ} {θ = θ} i
  = ass {γ = γ} {δ = δ} {θ = θ} i
  , sym ([∘] {t = t} {γ = δ} {δ = θ})i




∙-η  : γ ≡ ε
∙-η {γ = ε} = refl
