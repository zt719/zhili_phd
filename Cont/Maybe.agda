{-# OPTIONS --cubical #-}
module Cont.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
  renaming (Iso to _≅_)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Function.Base

open import Data.Pullback
open import Cont.Cont
open import Cont.Id

private
  variable
    X Y Z : Set

MaybeC : Cont
MaybeC = Bool ◃ λ{ false → ⊥ ; true → Unit }

Maybe : Set → Set
Maybe = ⟦ MaybeC ⟧

nothing : Maybe X
nothing = false , λ ()

just : X → Maybe X
just x = true , λ{ tt → x }

Maybe₁ : (X → Y) → Maybe X → Maybe Y
Maybe₁ = ⟦ MaybeC ⟧₁

ηC : Cont[ IdC , MaybeC ]
ηC = (λ{ tt → true}) ◃ λ{ tt tt → tt }

η : (X : Set) → X → Maybe X
η X x = ⟦ ηC ⟧₂ X (tt , λ{ tt → x })

module _ {X Y : Set} {f : X → Y} where

  ψη : X → Pullback (Maybe₁ f) (η Y)
  ψη x = η _ x , f x , (λ i → true , λ{ tt → f x })

  ψη⁻ : Pullback (Maybe₁ f) (η Y) → X
  ψη⁻ ((false , p) , y , eq) = ⊥-rec (true≢false (sym (cong ⟦_⟧.s eq)))
  ψη⁻ ((true , p) , y , eq) = p tt

  ψη-iso : X ≅ Pullback (Maybe₁ f) (η Y)
  ψη-iso ._≅_.fun = ψη
  ψη-iso ._≅_.inv = ψη⁻
  ψη-iso ._≅_.rightInv ((false , p) , y , eq) = ⊥-rec (true≢false (sym (cong ⟦_⟧.s eq)))
  ψη-iso ._≅_.rightInv ((true , p) , y , eq) i with ⟦_⟧.s (eq i)
  ... | false = {!!}
  ... | true = (true , p) , {!⟦_⟧.p (eq i) tt!} , {!!}
  ψη-iso ._≅_.leftInv a i = a
  {-
  Maybe₁ f (true , p)
  = true , λ{ tt → f (p tt) }
  = true , λ{ tt → y }
  = η Y y
  -}


module _ where
  open Cont[_,_] ηC
  open Cont IdC
  open Cont MaybeC renaming (S to T; P to Q)

  f⁻ : (s : S) → P s → Q (u s)
  f⁻ s tt = tt

  f-iso : (s : S) → Q (u s) ≅ P s
  f-iso s ._≅_.fun = f s
  f-iso s ._≅_.inv = f⁻ s
  f-iso s ._≅_.rightInv = λ b i → tt
  f-iso s ._≅_.leftInv = λ a i → tt

{-
MaybeMaybeC : Cont
MaybeMaybeC = MaybeC ∘c MaybeC

MaybeMaybe : Set → Set
MaybeMaybe = ⟦ MaybeMaybeC ⟧

μC : Cont[ MaybeMaybeC , MaybeC ]
μC = {!!}

μ : (X : Set) → MaybeMaybe X → Maybe X
μ = ⟦ μC ⟧₂

μ : (X : Set) → Maybe (Maybe X) → Maybe X
μ X x = {!!}

module _ where

  open Cont[_,_] μC
  open Cont MaybeMaybeC
  open Cont MaybeC renaming (S to T; P to Q)
  
  ff⁻ : (s : S) → P s → Q (u s)
  ff⁻ (true , snd₁) x = {!!}

  ff-iso : (s : S) → Q (u s) ≅ P s
  ff-iso s ._≅_.fun = f s
  ff-iso s ._≅_.inv = ff⁻ s
  ff-iso s ._≅_.rightInv = {!!}
  ff-iso s ._≅_.leftInv = {!!}
-}
