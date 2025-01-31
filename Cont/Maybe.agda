{-# OPTIONS --cubical #-}
module Cont.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
  renaming (Iso to _≅_)
open import Function.Base

open import Data.Pullback
open import Cont.Cont

open import Cubical.Data.Maybe

variable X Y Z : Set

fmap : (X → Y) → Maybe X → Maybe Y
fmap f nothing = nothing
fmap f (just x) = just (f x)

η : (X : Set) → X → Maybe X
η _ = just

μ : (X : Set) → Maybe (Maybe X) → Maybe X
μ _ nothing = nothing
μ _ (just mx) = mx

module _ {X Y : Set} {f : X → Y} where

  φη : X → Pullback (fmap f) (η Y)
  φη x = η _ x , f x , refl

  φη⁻ : Pullback (fmap f) (η Y) → X
  φη⁻ (nothing , y , eq) = ⊥-rec (¬nothing≡just eq)
  φη⁻ (just x , y , eq) = x

  φη-iso : X ≅ Pullback (fmap f) (η Y)
  φη-iso ._≅_.fun = φη
  φη-iso ._≅_.inv = φη⁻
  φη-iso ._≅_.rightInv = _
  φη-iso ._≅_.leftInv = λ a i → a

  φμ : Maybe (Maybe X) → Pullback (fmap f) (μ Y)
  φμ nothing = nothing , nothing , refl
  φμ (just nothing) = nothing , just nothing , refl
  φμ (just (just x)) = just x , just (just (f x)) , refl

  φμ⁻ : Pullback (fmap f) (μ Y) → Maybe (Maybe X)
  φμ⁻ (nothing , nothing , eq) = nothing
  φμ⁻ (nothing , just nothing , eq) = just nothing
  φμ⁻ (nothing , just (just y) , eq) = _
  φμ⁻ (just x , nothing , eq) = _
  φμ⁻ (just x , just nothing , eq) = _
  φμ⁻ (just x , just (just y) , eq) = just (just x)

  φμ-iso : Maybe (Maybe X) ≅ Pullback (fmap f) (μ Y)
  φμ-iso ._≅_.fun = φμ
  φμ-iso ._≅_.inv = φμ⁻
  φμ-iso ._≅_.rightInv = _
  φμ-iso ._≅_.leftInv nothing = refl
  φμ-iso ._≅_.leftInv (just nothing) = refl
  φμ-iso ._≅_.leftInv (just (just x)) = refl

IdC : Cont
IdC = Unit ◃ λ{ tt → Unit }

Id' : Set → Set
Id' = ⟦ IdC ⟧

MaybeC : Cont
MaybeC = Bool ◃ λ{ false → ⊥ ; true → Unit }

Maybe' : Set → Set
Maybe' = ⟦ MaybeC ⟧

nothing' : Maybe' X
nothing' = false , λ ()

just' : X → Maybe' X
just' x = true , λ{ tt → x }

fmap' : (X → Y) → Maybe' X → Maybe' Y
fmap' = ⟦ MaybeC ⟧₁

ηC : Cont[ IdC , MaybeC ]
ηC = (λ{ tt → true}) ◃ λ{ tt tt → tt }

η'' : (X : Set) → Id' X → Maybe' X
η'' = ⟦ ηC ⟧₂

η' : (X : Set) → X → Maybe' X
η' X x = η'' X (tt , λ{ tt → x })

module _ {X Y : Set} {f : X → Y} where

  ψη : X → Pullback (fmap' f) (η' Y)
  ψη x = (true , λ{ tt → x }) , (f x , λ i → true , λ{ tt → f x })

  ψη⁻ : Pullback (fmap' f) (η' Y) → X
  ψη⁻ ((false , p) , y , eq) = _
  ψη⁻ ((true , p) , y , eq) = p tt

  ψη-iso : X ≅ Pullback (fmap' f) (η' Y)
  ψη-iso ._≅_.fun = ψη
  ψη-iso ._≅_.inv = ψη⁻
  ψη-iso ._≅_.rightInv = _
  ψη-iso ._≅_.leftInv a i = a

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

MaybeMaybeC : Cont
MaybeMaybeC = MaybeC ∘c MaybeC

MaybeMaybe : Set → Set
MaybeMaybe = ⟦ MaybeMaybeC ⟧

nothing'' : MaybeMaybe X
nothing'' = (false , λ ()) , λ ()

justnothing : MaybeMaybe X
justnothing = (true , λ{ tt → false}) , λ ()

justjust : X → MaybeMaybe X
justjust x = (true , λ{ tt → true}) , λ (tt , tt) → x

{-
μC : Cont[ MaybeMaybeC , MaybeC ]
μC = {!!}

μ'' : (X : Set) → MaybeMaybe X → Maybe' X
μ'' = ⟦ μC ⟧₂

μ' : (X : Set) → Maybe' (Maybe' X) → Maybe' X
μ' X x = {!!}

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
