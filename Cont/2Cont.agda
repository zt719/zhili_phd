module Cont.2Cont where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

record 2Cont : Set₁ where
  inductive
  field
    S : Set
    P-X : S → Set
    P-F : S → Set
    R-F : (s : S) → P-F s → 2Cont

{-# NO_POSITIVITY_CHECK #-}
record ⟦_⟧ (2cont : 2Cont) (F : Set → Set) (X : Set) : Set where
  inductive
  open 2Cont 2cont
  field
    s : S
    p-f : (p : P-F s) → F (⟦ R-F s p ⟧ F X)
    p-a : P-X s → X

X : 2Cont
X = record
  { S = ⊤
  ; P-X = λ{ tt → ⊤ }
  ; P-F = λ{ tt → ⊥ }
  ; R-F = λ{ tt () }
  }

FX : 2Cont
FX = record
  { S = ⊤
  ; P-X = λ{ tt → ⊥ }
  ; P-F = λ{ tt → ⊤ }  
  ; R-F = λ{ tt tt → X }
  }

X×FFX : 2Cont
X×FFX = record
  { S = ⊤
  ; P-X = λ{ tt → ⊤ }
  ; P-F = λ{ tt → ⊤ }
  ; R-F = λ{ tt tt → FX }
  }

