module Cont.MonadTrans where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Data.List

open import Cont.HCont

variable
  X Y : Set

MaybeT : (Set → Set) → Set → Set
MaybeT M X = M (Maybe X)
{- = M (⊤ ⊎ X) -}

MaybeC : Nf ∙ (* ⇒ *)
MaybeC = lam (ne (S ◃ P ◃ R))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ *

  S : Set
  S = ⊤ ⊎ ⊤

  P : Var Γ₀ A → S → Set
  P vz (inj₁ tt) = ⊥
  P vz (inj₂ tt) = ⊤

  R : (x : Var Γ₀ A) (s : S) → P x s → Sp Γ₀ A *
  R vz (inj₂ tt) tt = ε

MaybeTC : Nf ∙ ((* ⇒ *) ⇒ * ⇒ *)
MaybeTC = lam (lam (napp M-Nf (napp (wkNf vz (wkNf vz MaybeC)) X-Nf)))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ * ⇒ * ▹ *

  M-Nf : Nf Γ₀ (* ⇒ *)
  M-Nf = nvar (vs vz)

  X-Nf : Nf Γ₀ *
  X-Nf = nvar vz
