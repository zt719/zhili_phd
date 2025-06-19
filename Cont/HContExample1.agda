module Cont.HContExample1 where

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum
open import Data.Product

open import Cont.HCont

private
  variable
    A B C : Ty

Γ₀ : Con
Γ₀ = • ▷ * ⇒ * ▷ *

X-Ne : Ne Γ₀ *
X-Ne = record { S = S ; P = P ; R = R }
  where
  S : Set
  S = ⊤

  P : Var Γ₀ A → S → Set
  P vz tt = ⊤
  P (vs vz) tt = ⊥

  R : (x : Var Γ₀ A) (s : S) (p : P x s) → Sp Γ₀ A *
  R vz tt tt = ε
  R (vs vz) tt ()

FX-Ne : Ne Γ₀ *
FX-Ne = record { S = S ; P = P ; R = R }
  where
  S : Set
  S = ⊤

  P : Var Γ₀ A → S → Set
  P vz tt = ⊥
  P (vs vz) tt = ⊤

  R : (x : Var Γ₀ A) (s : S) (p : P x s) → Sp Γ₀ A *
  R (vs vz) tt tt = ne X-Ne , ε

X×FFX-Ne : Ne Γ₀ *
X×FFX-Ne = record { S = S ; P = P ; R = R }
  where
  S : Set
  S = ⊤

  P : Var Γ₀ A → S → Set
  P vz tt = ⊤
  P (vs vz) tt = ⊤

  R : (x : Var Γ₀ A) (s : S) (p : P x s) → Sp Γ₀ A *
  R vz tt tt = ε
  R (vs vz) tt tt = (ne FX-Ne) , ε

⊤⊎FX-Ne : Ne Γ₀ *
⊤⊎FX-Ne = record { S = S ; P = P ; R = R }
  where
  S : Set
  S = Bool

  P : Var Γ₀ A → S → Set
  P vz _ = ⊥
  P (vs vz) false = ⊥
  P (vs vz) true = ⊤

  R : (x : Var Γ₀ A) (s : S) (p : P x s) → Sp Γ₀ A *
  R (vs vz) true tt = (ne X-Ne) , ε

-- H : (Set → Set) → Set → Set
-- H F X = X × F (F X)

H-HCont : HCont ((* ⇒ *) ⇒ * ⇒ *)
H-HCont = lam (lam (ne X×FFX-Ne))

-- J : (Set → Set) → Set → Set
-- J F X = ⊤ ⊎ F X

J-HCont : HCont ((* ⇒ *) ⇒ * ⇒ *)
J-HCont = lam (lam (ne ⊤⊎FX-Ne))

open Ne

H→J-NeHom : NeHom X×FFX-Ne ⊤⊎FX-Ne
H→J-NeHom = record { f = f ; g = g ; h = h }
  where
  f : X×FFX-Ne .S → ⊤⊎FX-Ne .S
  f tt = false

  g : (x : Var Γ₀ A) (s : X×FFX-Ne .S) → ⊤⊎FX-Ne .P x (f s) → X×FFX-Ne .P x s
  g (vs vz) tt ()

  h : (x : Var Γ₀ A) (s : X×FFX-Ne .S) (p : ⊤⊎FX-Ne .P x (f s)) →
      SpHom (X×FFX-Ne .R x s (g x s p)) (⊤⊎FX-Ne .R x (f s) p)
  h (vs vz) tt ()
  
H→J-HContHom : HContHom H-HCont J-HCont
H→J-HContHom = lam (lam (ne H→J-NeHom))
