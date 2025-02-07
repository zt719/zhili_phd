{-# OPTIONS --cubical #-}

open import Function.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
  renaming (Iso to _≅_)
open import Cubical.Data.Unit

open import Cont.Cont
open import Data.Pullback

module Cont.General where

postulate
  X Y : Set
  f : X → Y
  S : Set
  P : S → Set

MC : Cont
MC = S ◃ P

M : Set → Set
M = ⟦ MC ⟧

M₁ : {X Y : Set} → (X → Y) → M X → M Y
M₁ = ⟦ MC ⟧₁
  
T : Set
T = Unit
  
Q : Unit → Set
Q tt = Unit

IdC : Cont
IdC = T ◃ Q

Id : Set → Set
Id = ⟦ IdC ⟧

MCMC : Cont
MCMC = MC ∘c MC


postulate
  u : T → S
  g : (t : T) → P (u t) → Q t
  -- 𝐮 : Σ[ s ∈ S ] (P s → S) → S
  -- 𝐠 : (sf : Σ[ s ∈ S ] (P s → S)) → P (𝐮 sf) → Σ[ p ∈ P (fst sf) ] (P ((snd sf) p))

ηC : Cont[ IdC , MC ]
ηC = u ◃ g
  
η : (X : Set) → X → M X
η X x = ⟦ ηC ⟧₂ X (tt , λ{ tt → x })

{-
μC : Cont[ MC ∘c MC , MC ]
μC = 𝐮 ◃ 𝐠

μ : (X : Set) → M (M X) → M X
μ X (s , p) = ⟦ μC ⟧₂ X (({!!} , {!!}) , {!!})

postulate
  M-idl : (X : Set) → μ X ∘ η (M X) ≡ id
  M-idr : (X : Set) → μ X ∘ M₁ (η X) ≡ id
  M-ass : (X : Set) → μ X ∘ μ (M X) ≡ μ X ∘ M₁ (μ X)
-}

φ : X → Pullback (M₁ f) (η Y)
φ x = η _ x , f x , refl

{-
ψ : M (M X) → Pullback (M₁ f) (μ Y)
ψ mmx = μ _ mmx , M₁ (M₁ f) mmx , {!!}
-}

module _ 
  {g⁻ : (t : T) → Q t → P (u t)}
  {left : {t : T} → g t ∘ g⁻ t ≡ id}
  {right : {t : T} → g⁻ t ∘ g t ≡ id}
  where

  φ⁻ : Pullback (M₁ f) (η Y) → X
  φ⁻ ((s , p) , y , eq) = p (subst P {!!} (g⁻ tt tt))

  -- isPullback : X ≅ Pullback (M₁ f) (η Y)
  -- isPullback = {!!}

{-
module _
  {φ⁻ : Pullback (M₁ f) (η Y) → X}
  {left : φ ∘ φ⁻ ≡ id}
  {right : φ⁻ ∘ φ ≡ id}
  where

  g⁻ : (t : T) → Q t → P (u t)
  g⁻ tt tt = {!u tt!}
-}
