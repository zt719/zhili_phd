module Modal where

open import Data.String
open import Relation.Binary.PropositionalEquality

data Formula : Set where
  ⊥   : Formula                     -- false
  ⊤   : Formula                     -- true
  var : String → Formula             -- propositional variable
  ¬_  : Formula → Formula            -- negation
  _∧_ : Formula → Formula → Formula  -- conjunction
  _∨_ : Formula → Formula → Formula  -- disjunction
  _⇒_ : Formula → Formula → Formula  -- implication
  □_  : Formula → Formula            -- necessarily
  ◇_  : Formula → Formula            -- possibly
