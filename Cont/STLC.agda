{-# OPTIONS --type-in-type #-}

module Cont.STLC where

open import Cont.HCont
open import CWF.cwf-simple

open import Relation.Binary.PropositionalEquality
  hiding (subst)

private variable
  A B : Ty
  Γ Δ Θ : Con

data Tms : Con → Con → Set where
  ε : Tms Γ •
  _,_ : Tms Γ Δ → Nf Γ A → Tms Γ (Δ ▷ A)

subst : Nf Γ A → Tms Δ Γ → Nf Δ A
subst t ε = {!!}
subst t (us , u) = {!lam t!}

id : Tms Γ Γ
id = {!!}

_∘_ : Tms Δ Θ → Tms Γ Δ → Tms Γ Θ
ε ∘ us = ε
(ts , t) ∘ us = (ts ∘ us) , subst t us

HCont-STLC : CwF-simple
HCont-STLC .CwF-simple.Con = Con
HCont-STLC .CwF-simple.Ty = Ty
HCont-STLC .CwF-simple.Tm = Nf
HCont-STLC .CwF-simple.Tms = Tms
HCont-STLC .CwF-simple.id = id
HCont-STLC .CwF-simple._∘_ = _∘_
HCont-STLC .CwF-simple.idl = {!!}
HCont-STLC .CwF-simple.idr = {!!}
HCont-STLC .CwF-simple.ass = {!!}
HCont-STLC .CwF-simple._[_] = {!!}
HCont-STLC .CwF-simple.[id] = {!!}
HCont-STLC .CwF-simple.[∘] = {!!}
HCont-STLC .CwF-simple.• = •
HCont-STLC .CwF-simple.ε = ε
HCont-STLC .CwF-simple.•-η {δ = ε} = refl
HCont-STLC .CwF-simple._▷_ = _▷_
HCont-STLC .CwF-simple._,_ = _,_
HCont-STLC .CwF-simple.π₀ (ts , t) = ts
HCont-STLC .CwF-simple.π₁ (ts , t) = t
HCont-STLC .CwF-simple.▷-β₀ = refl
HCont-STLC .CwF-simple.▷-β₁ = refl
HCont-STLC .CwF-simple.▷-η {δ = ts , t} = refl
HCont-STLC .CwF-simple.π₀∘ = {!!}
HCont-STLC .CwF-simple.π₁∘ = {!!}
