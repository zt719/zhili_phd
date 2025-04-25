module Cont.HContNaive where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import Level

{- Syntax -}

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

private variable A B C : Ty

infixl 5 _▹_
data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

private variable Γ Δ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

private variable x y : Var Γ A

data Nf : Con → Ty → Set₁

record Ne (Γ : Con) : Set₁

data Sp : Con → Ty → Set₁

data Nf where
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)
  ne  : Ne Γ → Nf Γ *

private variable t u : Nf Γ A

record Ne Γ where
  inductive
  field
    S : Set
    -- P : Var Γ A → S → Set
    -- R : (x : Var Γ A) (s : S) → P x s → Sp Γ A
    PR : Var Γ A → S → Σ[ P ∈ Set ] (P → Sp Γ A)

  P : Var Γ A → S → Set
  P x s = PR x s .proj₁

  R : (x : Var Γ A) (s : S) → P x s → Sp Γ A
  R x s = PR x s .proj₂
open Ne

private variable m n : Ne Γ

data Sp where
  ε   : Sp Γ *
  _,_ : Nf Γ A → Sp Γ B → Sp Γ (A ⇒ B)

private variable ts us : Sp Γ A

HCont : Ty → Set₁
HCont A = Nf ∙ A


{- Semantics -}

⟦_⟧T : Ty → Set₁
⟦ * ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Con → Set₁
⟦ ∙ ⟧C = Lift (suc zero) ⊤
⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ vz ⟧v (γ , a) = a
⟦ vs x ⟧v (γ , a) = ⟦ x ⟧v γ

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦_⟧ne : Ne Γ → ⟦ Γ ⟧C → Set
⟦_⟧sp : Sp Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T → Set

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} record { S = S ; PR = PR } γ =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : PR x s .proj₁) → ⟦ PR x s .proj₂ p ⟧sp γ (⟦ x ⟧v γ))

⟦ ε ⟧sp γ a = a
⟦ n , ns ⟧sp γ f = ⟦ ns ⟧sp γ (f (⟦ n ⟧nf γ))

⟦_⟧ : HCont A → ⟦ A ⟧T
⟦ x ⟧ = ⟦ x ⟧nf (lift tt)
