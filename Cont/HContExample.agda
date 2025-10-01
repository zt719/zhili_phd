module Cont.HContExample where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum
open import Data.Product

open import Cont.HCont

Maybe : Set → Set
Maybe X = ⊤ ⊎ X

MaybeHCont : HCont (* ⇒ *)
MaybeHCont = lam (ne (record { S = S ; P = P ; R = R }))
  where
  S : Set
  S = Bool

  P : Var (∙ ▹ *) A → S → Set
  P vz false = ⊥
  P vz true = ⊤

  R : (x : Var (∙ ▹ *) A) (s : S) → P x s → Sp (∙ ▹ *) A *
  R vz true tt = ε

Maybe' : Set → Set
Maybe' = ⟦ MaybeHCont ⟧

H : (Set → Set) → (Set → Set)
H F X = X × F (F X)

H-HCont : HCont ((* ⇒ *) ⇒ * ⇒ *)
H-HCont = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  
  X-Nf : Nf (∙ ▹ * ⇒ * ▹ *) *
  X-Nf = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : Var (∙ ▹ * ⇒ * ▹ *) A → S → Set
    P vz tt = ⊤
    P (vs vz) tt = ⊥

    R : (x : Var (∙ ▹ * ⇒ * ▹ *) A) (s : S) (p : P x s)
      → Sp (∙ ▹ * ⇒ * ▹ *) A *
    R vz tt tt = ε
    R (vs vz) tt ()
    
  FX-Nf : Nf (∙ ▹ * ⇒ * ▹ *) *
  FX-Nf = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : Var (∙ ▹ * ⇒ * ▹ *) A → S → Set
    P vz tt = ⊥
    P (vs vz) tt = ⊤

    R : (x : Var (∙ ▹ * ⇒ * ▹ *) A) (s : S) (p : P x s)
      → Sp (∙ ▹ * ⇒ * ▹ *) A *
    R (vs vz) tt tt = X-Nf , ε
  
  S : Set
  S = ⊤
  
  P : Var (∙ ▹ * ⇒ * ▹ *) A → S → Set
  P vz tt = ⊤
  P (vs vz) tt = ⊤

  R : (x : Var (∙ ▹ * ⇒ * ▹ *) A) (s : S) (p : P x s)
    → Sp (∙ ▹ * ⇒ * ▹ *) A *
  R vz tt tt = ε
  R (vs vz) tt tt = FX-Nf , ε
--  R (vs vz) tt p = napp (nvar (vs vz)) (nvar vz) , ε

J : (Set → Set) → Set → Set
J F X = ⊤ ⊎ F X

J-HCont : HCont ((* ⇒ *) ⇒ * ⇒ *)
J-HCont = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  
  X-Nf : Nf (∙ ▹ * ⇒ * ▹ *) *
  X-Nf = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : Var (∙ ▹ * ⇒ * ▹ *) A → S → Set
    P vz tt = ⊤
    P (vs vz) tt = ⊥

    R : (x : Var (∙ ▹ * ⇒ * ▹ *) A) (s : S) (p : P x s)
      → Sp (∙ ▹ * ⇒ * ▹ *) A *
    R vz tt tt = ε
    R (vs vz) tt ()
  
  S : Set
  S = Bool
  
  P : Var (∙ ▹ * ⇒ * ▹ *) A → S → Set
  P vz false = ⊥
  P vz true = ⊥
  P (vs vz) false = ⊥
  P (vs vz) true = ⊤

  R : (x : Var (∙ ▹ * ⇒ * ▹ *) A) (s : S) (p : P x s)
    → Sp (∙ ▹ * ⇒ * ▹ *) A *
  R vz false ()
  R vz true ()
  R (vs vz) true tt = X-Nf , ε
