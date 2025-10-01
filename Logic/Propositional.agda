module Propositional where

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum

Prop = Set

variable
  P Q R : Prop

True : Prop
True = ⊤

False : Prop
False = ⊥

infixr 2 _⇒_
_⇒_ : Prop → Prop → Prop
P ⇒ Q = P → Q

infix  5 ¬_
¬_ : Prop → Prop
¬ P = P ⇒ False

infixl 4 _∧_
_∧_ : Prop → Prop → Prop
P ∧ Q = P × Q

infixl 3 _∨_
_∨_ : Prop → Prop → Prop
P ∨ Q = P ⊎ Q

infix  2 _⇔_
_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

-----

∧∨-distr : P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)
∧∨-distr = to , from
  where
  to : P ∧ (Q ∨ R) ⇒ (P ∧ Q) ∨ (P ∧ R)
  to (p , inj₁ q) = inj₁ (p , q)
  to (p , inj₂ r) = inj₂ (p , r)

  from : (P ∧ Q) ∨ (P ∧ R) ⇒ P ∧ (Q ∨ R)
  from (inj₁ (p , q)) = p , inj₁ q
  from (inj₂ (p , r)) = p , inj₂ r

dm₁ : ¬ (P ∨ Q) ⇔ ¬ P ∧ ¬ Q
dm₁ = to , from
  where
  to : ¬ (P ∨ Q) ⇒ ¬ P ∧ ¬ Q
  to ¬[p∨q] = (λ p → ¬[p∨q] (inj₁ p)) , (λ q → ¬[p∨q] (inj₂ q))

  from : ¬ P ∧ ¬ Q ⇒ ¬ (P ∨ Q)
  from (¬p , ¬q) (inj₁ p) = ¬p p
  from (¬p , ¬q) (inj₂ q) = ¬q q

nnlem : ¬ ¬ (P ∨ ¬ P)
nnlem ¬[p∨¬p] = ¬[p∨¬p] (inj₂ (λ p → ¬[p∨¬p] (inj₁ p)))

nn : P ⇒ ¬ ¬ P
nn p ¬p = ¬p p

n-impl : (P ⇒ Q) ⇒ ¬ Q ⇒ ¬ P
n-impl p⇒q ¬p p = ¬p (p⇒q p)

{- Classical -}

postulate
  lem : P ∨ ¬ P
  dne : ¬ ¬ P → P
  pl : ((P → Q) → P) → P

dm₂ : ¬ (P ∧ Q) ⇔ ¬ P ∨ ¬ Q
dm₂ {P} {Q} = to , from
  where
  to : ¬ (P ∧ Q) ⇒ ¬ P ∨ ¬ Q
  to ¬[p∧q] with lem {P}
  ... | inj₁ p = inj₂ (λ q → ¬[p∧q] (p , q))
  ... | inj₂ ¬p = inj₁ (λ p → ¬p p)

  from : ¬ P ∨ ¬ Q ⇒ ¬ (P ∧ Q)
  from (inj₁ ¬p) (p , q) = ¬p p
  from (inj₂ ¬q) (p , q) = ¬q q

dne′ : ¬ ¬ P → P
dne′ {P} ¬¬p with lem {P}
dne′ ¬¬p | inj₁ p = p
dne′ ¬¬p | inj₂ ¬p with ¬¬p ¬p
dne′ ¬¬p | inj₂ ¬p | ()

lem′ : P ∨ ¬ P
lem′ = dne nnlem
