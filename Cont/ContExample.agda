module Cont.ContExample where

open import Data.Empty
open import Data.Unit
open import Data.Bool hiding (T)
open import Data.Nat
open import Data.Fin

open import Cont.Cont

MaybeCont : Cont
MaybeCont = Bool ◃ λ{ false → ⊥ ; true → ⊤ }

Maybe : Set → Set
Maybe = ⟦ MaybeCont ⟧

ListCont : Cont
ListCont = ℕ ◃ Fin

List : Set → Set
List = ⟦ ListCont ⟧

M⇒L-M : ContHom MaybeCont ListCont
M⇒L-M = f ◃ g
  where
  open Cont MaybeCont
  open Cont ListCont renaming (S to T; P to Q)
  f : S → T
  f false = zero
  f true = suc zero

  g : (s : S) → Q (f s) → P s
  g true zero = tt

M⇒L : (X : Set) → Maybe X → List X
M⇒L = ⟦ M⇒L-M ⟧₂
