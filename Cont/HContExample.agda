module Cont.HContExample where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Nat hiding (_*_)
open import Data.Fin

open import Cont.HCont

private
  variable
    A B C : Ty

MaybeHCont : HCont (* ⇒ *)
MaybeHCont = lam (ne (record { S = S ; P = P ; R = R }))
  where
  S : Set
  S = Bool

  P : S → Var (• ▷ *) A → Set
  P false vz = ⊥
  P true vz = ⊤

  R : (s : S) (x : Var (• ▷ *) A) → P s x → Sp (• ▷ *) A *
  R true vz tt = ε

ListHCont : HCont (* ⇒ *)
ListHCont = lam (ne (record { S = S ; P = P ; R = R }))
  where
  S : Set
  S = ℕ

  P : S → Var (• ▷ *) A → Set
  P n vz = Fin n

  R : (s : S) (x : Var (• ▷ *) A) → P s x → Sp (• ▷ *) A *
  R n vz i = ε

L : (Set → Set) → (Set → Set)
L F X = ⊤ ⊎ X × F X

L-HCont : HCont ((* ⇒ *) ⇒ * ⇒ *)
L-HCont = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  X-Nf : Nf (• ▷ * ⇒ * ▷ *) *
  X-Nf = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : S → Var (• ▷ * ⇒ * ▷ *) A → Set
    P tt vz = ⊤
    P tt (vs _) = ⊥

    R : (s : S) (x : Var (• ▷ * ⇒ * ▷ *) A) →
      P s x → Sp (• ▷ * ⇒ * ▷ *) A *
    R tt vz tt = ε
    
  S : Set
  S = Bool

  P : S → Var (• ▷ * ⇒ * ▷ *) A → Set
  P false x = ⊥
  P true x = ⊤

  R : (s : S) (x : Var (• ▷ * ⇒ * ▷ *) A) →
    P s x → Sp (• ▷ * ⇒ * ▷ *) A *
  R true vz tt = ε
  R true (vs vz) tt = X-Nf , ε

H : (Set → Set) → (Set → Set)
H F X = X × F (F X)

H-HCont : HCont ((* ⇒ *) ⇒ * ⇒ *)
H-HCont = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  Γ₀ : Con
  Γ₀ = • ▷ * ⇒ * ▷ *

  X-Nf : Nf Γ₀ *
  X-Nf = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : S → Var Γ₀ A → Set
    P tt vz = ⊤
    P tt (vs vz) = ⊥

    R : (s : S) (x : Var Γ₀ A) → P s x → Sp Γ₀ A *
    R tt vz tt = ε
    R tt (vs vz) ()
    
  FX-Nf : Nf Γ₀ *
  FX-Nf = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : S → Var Γ₀ A → Set
    P tt vz = ⊥
    P tt (vs vz) = ⊤

    R : (s : S) (x : Var Γ₀ A) → P s x → Sp Γ₀ A *
    R tt (vs vz) tt = X-Nf , ε
    
  S : Set
  S = ⊤
  
  P : S → Var Γ₀ A → Set
  P tt vz = ⊤
  P tt (vs vz) = ⊤

  R : (s : S) (x : Var Γ₀ A) (p : P s x) → Sp Γ₀ A *
  R tt vz tt = ε
  R tt (vs vz) p = FX-Nf , ε
