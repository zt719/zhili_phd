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
  { fmap = λ{ f (inl tt) → inl tt ; f (inr x) → inr (f x) }
  ; fmapid = λ{ i (inl tt) → inl tt ; i (inr x) → inr x }
  ; fmap∘ = λ{ f g i (inl tt) → inl tt ; f g i (inr x) → inr (f (g x)) }
  }

B : ⟦ (* ⇒ *) ⇒ (* ⇒ *) ⟧T
B F X = X × F (F X)

FuncB : ⟦ (* ⇒ *) ⇒ (* ⇒ *) ⟧Func B
FuncB = BB , BBB
  where
  open Func
  
  BB : (F : Set → Set) → ⟦ * ⇒ * ⟧Func F → ⟦ * ⇒ * ⟧Func (B F)
  BB F (_ , record { fmap = fmap ; fmapid = fmapid ; fmap∘ = fmap∘ }) = _ , record
    { fmap = λ f (x , ffx) → f x , fmap (fmap f) ffx
    ; fmapid = λ i (x , ffx) → x , (cong fmap fmapid ∙ fmapid) i ffx
    ; fmap∘ = λ f g i (x , ffx) → f (g x) , (cong fmap (fmap∘ f g) ∙ fmap∘ (fmap f) (fmap g)) i ffx
    }

  BBB : Func ⟦ * ⇒ * ⟧Cat ⟦ * ⇒ * ⟧Cat _
  BBB .fmap {F , _ , FF} {G , _ , GG} record { η = η ; nat = nat }
    = record
    { η = λ (X , _) (x , ffx) → x , η (G X , tt) (fmap FF (η (X , tt)) ffx)
    ; nat = λ f i (x , ffx) → f x , aux f i ffx
    }
    where
      open Cat ⟦ * ⟧Cat
      aux : {X Y : Set} (f : X → Y)
        → fmap GG (fmap GG f) ∘ η (G X , tt) ∘ fmap FF (η (X , tt))
        ≡ η (G Y , tt) ∘ fmap FF (η (Y , tt)) ∘ fmap FF (fmap FF f)
      aux {X} {Y} f =
        fmap GG (fmap GG f) ∘ η (G X , tt) ∘ fmap FF (η (X , tt))
          ≡⟨ cong (fmap GG (fmap GG f) ∘_) (sym (nat (η (X , tt)))) ⟩
        fmap GG (fmap GG f) ∘ fmap GG (η (X , tt)) ∘ η (F X , tt)
          ≡⟨ cong (_∘ η (F X , tt)) (sym (fmap∘ GG (fmap GG f) (η (X , tt)))) ⟩
        fmap GG (fmap GG f ∘ η (X , tt)) ∘ η (F X , tt)
          ≡⟨ cong (_∘ η (F X , tt)) (cong (fmap GG) (nat f)) ⟩
        fmap GG (η (Y , tt) ∘ fmap FF f) ∘ η (F X , tt)
          ≡⟨ cong (_∘ η (F X , tt)) (fmap∘ GG (η (Y , tt)) (fmap FF f)) ⟩
        fmap GG (η (Y , tt)) ∘ fmap GG (fmap FF f) ∘ η (F X , tt)
          ≡⟨ cong (fmap GG (η (Y , tt)) ∘_) (nat (fmap FF f)) ⟩
        fmap GG (η (Y , tt)) ∘ η (F Y , tt) ∘ fmap FF (fmap FF f)
          ≡⟨ cong (_∘ fmap FF (fmap FF f)) (nat (η (Y , tt))) ⟩
        η (G Y , tt) ∘ fmap FF (η (Y , tt)) ∘ fmap FF (fmap FF f)
          ∎

  BBB .fmapid {F , _ , FF} = Nat≡ (λ i (X , _) (x , ffx) → x , fmapid FF i ffx)

  BBB .fmap∘ {F , _ , FF} {G , _ , GG} {H , _ , HH}
    record { η = η₁ ; nat = nat₁ }
    record { η = η₂ ; nat = nat₂ }
    = Nat≡ (λ i (X , _) (x , ffx) → x , aux i ffx)
    where
      open Cat ⟦ * ⟧Cat
      aux : {X : Set}
        → η₁ (H X , tt) ∘ η₂ (H X , tt) ∘ fmap FF(η₁ (X , tt) ∘ η₂ (X , tt))
        ≡ η₁ (H X , tt) ∘ fmap GG (η₁ (X , tt)) ∘ η₂ (G X , tt) ∘ fmap FF (η₂ (X , tt))
      aux {X} =
        η₁ (H X , tt) ∘ η₂ (H X , tt) ∘ fmap FF (η₁ (X , tt) ∘ η₂ (X , tt))
          ≡⟨ cong ((η₁ (H X , tt) ∘ η₂ (H X , tt)) ∘_) (fmap∘ FF (η₁ (X , tt)) (η₂ (X , tt))) ⟩
        η₁ (H X , tt) ∘ η₂ (H X , tt) ∘ fmap FF (η₁ (X , tt)) ∘ fmap FF (η₂ (X , tt))
          ≡⟨ cong (η₁ (H X , tt) ∘_) (cong (_∘ fmap FF (η₂ (X , tt))) (sym (nat₂ (η₁ (X , tt))))) ⟩
        η₁ (H X , tt) ∘ fmap GG (η₁ (X , tt)) ∘ η₂ (G X , tt) ∘ fmap FF (η₂ (X , tt)) ∎

L : ⟦ (* ⇒ *) ⇒ (* ⇒ *) ⟧T
L F X = ⊤ ⊎ (X × F X)

FuncL : ⟦ (* ⇒ *) ⇒ (* ⇒ *) ⟧Func L
FuncL = LL , LLL
  where
  open Func
  LL : (F : Set → Set) → ⟦ * ⇒ * ⟧Func F → ⟦ * ⇒ * ⟧Func (L F)
  LL F (_ , record { fmap = fmap ; fmapid = fmapid ; fmap∘ = fmap∘ }) = _ , record
    { fmap = λ{ f (inl tt) → inl tt ; f (inr (x , fx)) → inr (f x , fmap f fx) }
    ; fmapid = λ{ i (inl tt) → inl tt ; i (inr (x , fx)) → inr (x , fmapid i fx) }
    ; fmap∘ = λ{ f g i (inl tt) → inl tt ; f g i (inr (x , fx)) → inr (f (g x) , fmap∘ f g i fx) }
    }

  LLL : Func ⟦ * ⇒ * ⟧Cat ⟦ * ⇒ * ⟧Cat _
  LLL .fmap {F , _ , FF} {G , _ , GG} record { η = η ; nat = nat } = record
    { η = λ{ (X , _) (inl tt) → inl tt ; (X , _) (inr (x , fx)) → inr (x , η (X , tt) fx) }
    ; nat = λ{ f i (inl tt) → inl tt ; f i (inr (x , fx)) → inr (f x , nat f i fx) }
    }
    
  LLL .fmapid {F , _ , FF} = Nat≡ λ{ i (X , _) (inl tt) → inl tt ; i (X , _) (inr (x , fx)) → inr (x , fx) }
  
  LLL .fmap∘ {F , _ , FF} {G , _ , GG} {H , _ , HH}
    record { η = η₁ ; nat = nat₁ }
    record { η = η₂ ; nat = nat₂ }
    = Nat≡ λ{ i (X , _) (inl tt) → inl tt ; i (X , _) (inr (x , fx)) → inr (x , η₁ (X , tt) (η₂ (X , tt) fx)) }
