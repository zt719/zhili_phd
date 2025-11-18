{-# OPTIONS --guardedness #-}

module Cont.2Cont-LList where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Cont.Cont

record 2Cont : Set₁ where
  inductive
  pattern
  constructor _◃_+_+_
  
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

ℍ²ᶜ : 2Cont
ℍ²ᶜ = (⊤ ⊎ ⊤) ◃ (λ{ (inj₁ tt) → ⊥ ; (inj₂ tt) → ⊤ })
  + (λ{ (inj₁ tt) → ⊥ ; (inj₂ tt) → ⊤ })
  + λ{ (inj₂ tt) tt → FX²ᶜ }
  where
  FX²ᶜ : 2Cont
  FX²ᶜ = ⊤ ◃ (λ{ tt → ⊥ }) + (λ{ tt → ⊤ }) + λ{ tt tt → X²ᶜ }
    where
    X²ᶜ : 2Cont
    X²ᶜ = ⊤ ◃ (λ{ tt → ⊤ }) + (λ{ tt → ⊥ }) + λ{ tt () }

appS : 2Cont → Cont → Set
appS (S ◃ _ + PF + RF) (T ◃ Q) = Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pf) (T ◃ Q)))

appP : (H : 2Cont) (F : Cont) → appS H F → Set
appP (S ◃ PX + PF + RF) (T ◃ Q) (s , f) = Σ[ pf ∈ PF s ] let (t , g) = f pf in Σ[ q ∈ Q t ] (appP (RF s pf) (T ◃ Q) (g q) ⊎ PX s) 

app : 2Cont → Cont → Cont
app H F = appS H F ◃ appP H F

data S : Set

P : S → Set

data S where
  leaf : S
  node : (s : S) (f : P s → S) → S

P leaf = ⊥
P (node s f) = ⊤ ⊎ Σ[ p ∈ P s ] P (f p)

  -- app ℍ²ᶜ LListᶜ → app ℍ²ᶜ UV
  --       ↓               ↓
  --     LListᶜ     →     UV

S' : Set
S' = appS ℍ²ᶜ (S ◃ P)

P' : S' → Set
P' = appP ℍ²ᶜ (S ◃ P)

{-
H F X = ⊤ ⊎ X × F (H₁ F X)
H₁ F X = F (H₂ F X)
H₂ F X = X
-}

inS : S' → S
inS (inj₁ tt , _) = leaf
inS (inj₂ tt , k) = node (k tt .proj₁)
  (λ p → k tt .proj₂ p .proj₂ tt .proj₁)

inP : (s' : S') → P (inS s') → P' s'
inP (inj₁ tt , k) ()
inP (inj₂ tt , k) (inj₁ tt) = tt , {!!} , {!!}
inP (inj₂ tt , k) (inj₂ (p , pfp)) = tt , {!!} , {!!}

inSP : (S' ◃ P') →ᶜ (S ◃ P)
inSP = inS ◃ inP

module _ (T : Set) (Q : T → Set) where

  T' : Set
  T' = ⊤ ⊎ Σ[ t ∈ T ] (Q t → T)

  Q' : T' → Set
  Q' (inj₁ tt) = ⊥
  Q' (inj₂ (t , f)) = ⊤ ⊎ Σ[ q ∈ Q t ] Q (f q)

  module _ (inT : T' → T) (inQ : (t' : T') → Q (inT t') → Q' t') where
