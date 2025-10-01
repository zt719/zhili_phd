module Cont.IHCont where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base hiding (_$_)
open import Relation.Binary.PropositionalEquality hiding (J; [_])

{-- Syntax --}

variable J : Set
  
{- Types & Contexts & Variables -}

infixr 20 _⇒_
data Ty : Set where
  * : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

infixl 5 _▹_
data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

variable Γ Δ Θ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y : Var Γ A

{- Indexed Normal Forms -}

infixr 4 _,_

data JNf : Con → Ty → Set → Set₁

record JNe (Γ : Con) (B : Ty) (J : Set) : Set₁

data JSp : Con → Ty → Ty → Set → Set₁

data JNf where
  lam : JNf (Γ ▹ A) B J → JNf Γ (A ⇒ B) J
  ne  : JNe Γ * J → JNf Γ * J

variable t u w : JNf Γ A J

record JNe Γ B J where
  constructor _◃_◃_
  inductive
  field
    S : Set
    P : J → Var Γ A → S → Set
    R : (j : J) (x : Var Γ A) (s : S) → P j x s → JSp Γ A B J

variable spr tql : JNe Γ A J

data JSp where
  ε   : JSp Γ A A J
  _,_ : JNf Γ A J → JSp Γ B C J → JSp Γ (A ⇒ B) C J
  
variable ts us ws : JSp Γ A B J

JHCont : Ty → Set → Set₁
JHCont = JNf ∙

open import Data.Nat
open import Data.Fin

{- Example -}

data JH (F : Set → Set) (X : Set) : ℕ → ℕ → Set where
  [] : JH F X zero zero
  _∷₀_ : ∀ {m n} → X → JH F X m n → JH F X m (suc n)
  _∷₁_ : ∀ {m n} → F X → JH F X m n → JH F X (suc m) n

JH-JHCont : JHCont ((* ⇒ *) ⇒ (* ⇒ *)) (ℕ × ℕ)
JH-JHCont = lam (lam (ne ({!!} ◃ {!!} ◃ {!!})))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ * ⇒ * ▹ *

  S : Set
  S = {!!}
