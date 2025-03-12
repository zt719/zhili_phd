{-# OPTIONS --type-in-type #-}

module Cont.HCont2 where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

{- Syntax -}

infixr 20 _⇒_
data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

infixl 5 _▹_

variable A B C : Ty
variable Γ Δ : Con

data Var : Con → Ty → Set where
  zero : Var (Γ ▹ A) A
  suc  : Var Γ A → Var (Γ ▹ B) A

data HCont-NF : Con → Ty → Set

record HCont-NE (Γ : Con) : Set

data HCont-SP : Con → Ty → Set

data HCont-NF where
  lam : HCont-NF (Γ ▹ A) B → HCont-NF Γ (A ⇒ B)
  ne  : HCont-NE Γ → HCont-NF Γ set

record HCont-NE Γ where
  inductive
  field
    S : Set
    P : S → Var Γ A → Set
    R : (s : S) (x : Var Γ A) (p : P s x) → HCont-SP Γ A

data HCont-SP where
  ε   : HCont-SP Γ set
  _,_ : HCont-NF Γ A → HCont-SP Γ B → HCont-SP Γ (A ⇒ B)

HCont : Ty → Set
HCont A = HCont-NF ∙ A

H : (Set → Set) → (Set → Set)
H F A = A × F (F A)

BCont : HCont ((set ⇒ set) ⇒ set ⇒ set)
BCont = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ set ⇒ set ▹ set

  NE-A : HCont-NE Γ₀
  NE-A = record { S = S ; P = P ; R = R }
    where
    S : Set
    S = ⊤

    P : S → Var Γ₀ A → Set
    P tt zero = ⊤
    P tt (suc zero) = ⊥

    R : (s : S) (x : Var Γ₀ A) → P s x → HCont-SP Γ₀ A
    R tt zero tt = ε
    R tt (suc zero) ()
  
  NE-FA : HCont-NE Γ₀
  NE-FA = record { S = S ; P = P ; R = R }
    where
    S : Set
    S = ⊤

    P : S → Var Γ₀ A → Set
    P tt zero = ⊥
    P tt (suc zero) = ⊤

    R : (s : S) (x : Var Γ₀ A) → P s x → HCont-SP Γ₀ A
    R tt zero ()
    R tt (suc zero) tt = ne NE-A , ε

  
  S : Set
  S = ⊤

  P : S → Var Γ₀ A → Set
  P tt zero = ⊤
  P tt (suc zero) = ⊤

  R : (s : S) (x : Var Γ₀ A) → P s x → HCont-SP Γ₀ A
  R tt zero tt = ε
  R tt (suc zero) tt = ne NE-FA , ε


----

open import Cont.Cont

HCont→Cont : HCont (set ⇒ set) → Cont
HCont→Cont (lam (ne record { S = S ; P = P ; R = R })) = S ◃ λ s → P s zero

Cont→HCont : Cont → HCont (set ⇒ set)
Cont→HCont (S ◃ P) = lam (ne (record { S = S ; P = λ{ s zero → P s } ; R = λ{ s zero p → ε } }))

----

⟦_⟧T : Ty → Set
⟦ set ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Con → Set
⟦ ∙ ⟧C = ⊤
⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ zero ⟧v (γ , a) = a
⟦ suc x ⟧v (γ , a) = ⟦ x ⟧v γ

⟦_⟧nf : HCont-NF Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦_⟧ne : HCont-NE Γ → ⟦ Γ ⟧C → Set
⟦_⟧sp : HCont-SP Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T → Set

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))

⟦ ε ⟧sp γ a = a
⟦ n , ns ⟧sp γ f = ⟦ ns ⟧sp γ (f (⟦ n ⟧nf γ))

⟦_⟧hcont : HCont A → ⟦ A ⟧T
⟦ x ⟧hcont = ⟦ x ⟧nf tt

B-HCont : (Set → Set) → Set → Set
B-HCont = ⟦ BCont ⟧hcont

{-
= ⟦ lam (lam (ne (record { S = S ; P = P ; R = R }))) ⟧hcont
= ⟦ lam (lam (ne (record { S = S ; P = P ; R = R }))) ⟧nf tt
= λ F → ⟦ lam (ne (record { S = S ; P = P ; R = R })) ⟧nf (tt , F)
= λ F X → ⟦ ne (record { S = S ; P = P ; R = R }) ⟧nf (tt , F , X)
= λ F X → ⟦ record { S = S ; P = P ; R = R } ⟧ne (tt , F , X)
= λ F X → ⟦ record { S = S ; P = P ; R = R } ⟧ne (tt , F , A)
= λ F X → Σ[ s ∈ S ] ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))   # γ = tt , F , X

  Σ[ s ∈ S ] ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))
= ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))                # S = ⊤
= ⟦ R tt zero tt ⟧sp γ (⟦ zero ⟧v γ) × ⟦ R tt one tt ⟧sp γ (⟦ one ⟧v γ))  # P tt zero = ⊤ , P tt one = ⊤
= ⟦ ε ⟧sp γ (⟦ zero ⟧v γ) × ⟦ ne FFA , ε ⟧sp γ (⟦ one ⟧v γ)               # R ...
= ⟦ zero ⟧v γ × ⟦ ε ⟧sp γ (⟦ one ⟧v γ (⟦ ne NE-FA ⟧nf γ))
= X × ⟦ one ⟧v γ (⟦ ne NE-FA ⟧nf γ)
= X × F (⟦ ne NE-FA ⟧nf γ)
= X × F (⟦ NE-FA ⟧ne γ)

  ⟦ NE-FA ⟧ne γ
= ⟦ record { S = S ; P = P ; R = R } ⟧ne γ
= Σ[ s ∈ S ] ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))   # by definition of S , P , R
= ⟦ ne NE-A , ε ⟧sp γ (⟦ one ⟧v γ)
= ⟦ ε ⟧sp γ (⟦ one ⟧v γ (⟦ ne NE-A ⟧nf γ))
= ⟦ one ⟧v γ (⟦ ne NE-A ⟧nf γ)
= F (⟦ ne NE-A ⟧nf γ)

  ⟦ ne NE-A ⟧nf γ
= ⟦ record { S = S ; P = P ; R = R } ⟧ne γ
= Σ[ s ∈ S ] ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))   # by definition of S , P , R
= ⟦ ε ⟧γ (⟦ zero ⟧v γ)
= ⟦ zero ⟧v γ
= A
-}
