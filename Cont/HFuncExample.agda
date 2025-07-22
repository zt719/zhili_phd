{-# OPTIONS --type-in-type --cubical #-}

module Cont.HFuncExample where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cont.HFunc

N : ⟦ * ⇒ * ⟧T
N X = ⊤ ⊎ X

FuncN : ⟦ * ⇒ * ⟧Func N
FuncN = _ , record
  { F₁ = λ (lift f) → lift λ{ (inl tt) → inl tt ; (inr x) → inr (f x) }
  ; F-id = λ i → lift {!!}   ; F-∘ = {!!} }

{-
FuncN : ⟦ * ⇒ * ⟧Func N
FuncN = _ , record
  { F₁ = λ{ f (inl tt) → inl tt ; f (inr x) → inr (f x) }
  ; F-id = λ{ i (inl tt) → inl tt ; i (inr x) → inr x }
  ; F-∘ = λ{ f g i (inl tt) → inl tt ; f g i (inr x) → inr (f (g x)) }
  }
-}

B : ⟦ (* ⇒ *) ⇒ (* ⇒ *) ⟧T
B F X = X × F (F X)

{-
FuncB : ⟦ (* ⇒ *) ⇒ (* ⇒ *) ⟧Func B
FuncB = BB , BBB
  where
  open Func
  
  BB : (F : Set → Set) → ⟦ * ⇒ * ⟧Func F → ⟦ * ⇒ * ⟧Func (B F)
  BB F (_ , record { F₁ = F₁ ; F-id = F-id ; F-∘ = F-∘ })
    = _ , record
    { F₁ = λ f (x , ffx) → f x , F₁ (F₁ f) ffx
    ; F-id = λ i (x , ffx) → x , (cong F₁ F-id ∙ F-id) i ffx
    ; F-∘ = λ f g i (x , ffx) → f (g x) , (cong F₁ (F-∘ f g) ∙ F-∘ (F₁ f) (F₁ g)) i ffx
    }

  BBB : Func ⟦ * ⇒ * ⟧Cat ⟦ * ⇒ * ⟧Cat _
  BBB .F₁ {F , _ , FF} {G , _ , GG} record { η = η ; nat = nat }
    = record
    { η = λ (X , _) (x , ffx) → x , η (G X , tt) (F₁ FF (η (X , tt)) ffx)
    ; nat = λ f i (x , ffx) → f x , aux f i ffx
    }
    where
      open Cat ⟦ * ⟧Cat
      aux : {X Y : Set} (f : X → Y)
        → F₁ GG (F₁ GG f) ∘ η (G X , tt) ∘ F₁ FF (η (X , tt))
        ≡ η (G Y , tt) ∘ F₁ FF (η (Y , tt)) ∘ F₁ FF (F₁ FF f)
      aux {X} {Y} f =
        F₁ GG (F₁ GG f) ∘ η (G X , tt) ∘ F₁ FF (η (X , tt))
          ≡⟨ cong (F₁ GG (F₁ GG f) ∘_) (sym (nat (η (X , tt)))) ⟩
        F₁ GG (F₁ GG f) ∘ F₁ GG (η (X , tt)) ∘ η (F X , tt)
          ≡⟨ cong (_∘ η (F X , tt)) (sym (F-∘ GG (F₁ GG f) (η (X , tt)))) ⟩
        F₁ GG (F₁ GG f ∘ η (X , tt)) ∘ η (F X , tt)
          ≡⟨ cong (_∘ η (F X , tt)) (cong (F₁ GG) (nat f)) ⟩
        F₁ GG (η (Y , tt) ∘ F₁ FF f) ∘ η (F X , tt)
          ≡⟨ cong (_∘ η (F X , tt)) (F-∘ GG (η (Y , tt)) (F₁ FF f)) ⟩
        F₁ GG (η (Y , tt)) ∘ F₁ GG (F₁ FF f) ∘ η (F X , tt)
          ≡⟨ cong (F₁ GG (η (Y , tt)) ∘_) (nat (F₁ FF f)) ⟩
        F₁ GG (η (Y , tt)) ∘ η (F Y , tt) ∘ F₁ FF (F₁ FF f)
          ≡⟨ cong (_∘ F₁ FF (F₁ FF f)) (nat (η (Y , tt))) ⟩
        η (G Y , tt) ∘ F₁ FF (η (Y , tt)) ∘ F₁ FF (F₁ FF f)
          ∎

  BBB .F-id {F , _ , FF} = Nat≡ (λ i (X , _) (x , ffx) → x , F-id FF i ffx)

  BBB .F-∘ {F , _ , FF} {G , _ , GG} {H , _ , HH}
    record { η = η₁ ; nat = nat₁ }
    record { η = η₂ ; nat = nat₂ }
    = Nat≡ (λ i (X , _) (x , ffx) → x , aux i ffx)
    where
      open Cat ⟦ * ⟧Cat
      aux : {X : Set}
        → η₁ (H X , tt) ∘ η₂ (H X , tt) ∘ F₁ FF(η₁ (X , tt) ∘ η₂ (X , tt))
        ≡ η₁ (H X , tt) ∘ F₁ GG (η₁ (X , tt)) ∘ η₂ (G X , tt) ∘ F₁ FF (η₂ (X , tt))
      aux {X} =
        η₁ (H X , tt) ∘ η₂ (H X , tt) ∘ F₁ FF (η₁ (X , tt) ∘ η₂ (X , tt))
          ≡⟨ cong ((η₁ (H X , tt) ∘ η₂ (H X , tt)) ∘_) (F-∘ FF (η₁ (X , tt)) (η₂ (X , tt))) ⟩
        η₁ (H X , tt) ∘ η₂ (H X , tt) ∘ F₁ FF (η₁ (X , tt)) ∘ F₁ FF (η₂ (X , tt))
          ≡⟨ cong (η₁ (H X , tt) ∘_) (cong (_∘ F₁ FF (η₂ (X , tt))) (sym (nat₂ (η₁ (X , tt))))) ⟩
        η₁ (H X , tt) ∘ F₁ GG (η₁ (X , tt)) ∘ η₂ (G X , tt) ∘ F₁ FF (η₂ (X , tt)) ∎

L : ⟦ (* ⇒ *) ⇒ (* ⇒ *) ⟧T
L F X = ⊤ ⊎ (X × F X)

FuncL : ⟦ (* ⇒ *) ⇒ (* ⇒ *) ⟧Func L
FuncL = LL , LLL
  where
  open Func
  LL : (F : Set → Set) → ⟦ * ⇒ * ⟧Func F → ⟦ * ⇒ * ⟧Func (L F)
  LL F (_ , record { F₁ = F₁ ; F-id = F-id ; F-∘ = F-∘ }) = _ , record
    { F₁ = λ{ f (inl tt) → inl tt ; f (inr (x , fx)) → inr (f x , F₁ f fx) }
    ; F-id = λ{ i (inl tt) → inl tt ; i (inr (x , fx)) → inr (x , F-id i fx) }
    ; F-∘ = λ{ f g i (inl tt) → inl tt ; f g i (inr (x , fx)) → inr (f (g x) , F-∘ f g i fx) }
    }

  LLL : Func ⟦ * ⇒ * ⟧Cat ⟦ * ⇒ * ⟧Cat _
  LLL .F₁ {F , _ , FF} {G , _ , GG} record { η = η ; nat = nat } = record
    { η = λ{ (X , _) (inl tt) → inl tt ; (X , _) (inr (x , fx)) → inr (x , η (X , tt) fx) }
    ; nat = λ{ f i (inl tt) → inl tt ; f i (inr (x , fx)) → inr (f x , nat f i fx) }
    }
    
  LLL .F-id {F , _ , FF} = Nat≡ λ{ i (X , _) (inl tt) → inl tt ; i (X , _) (inr (x , fx)) → inr (x , fx) }
  
  LLL .F-∘ {F , _ , FF} {G , _ , GG} {H , _ , HH}
    record { η = η₁ ; nat = nat₁ }
    record { η = η₂ ; nat = nat₂ }
    = Nat≡ λ{ i (X , _) (inl tt) → inl tt ; i (X , _) (inr (x , fx)) → inr (x , η₁ (X , tt) (η₂ (X , tt) fx)) }
-}
