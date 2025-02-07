{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓ'' : Level

ac : {A : Type ℓ} {B : A → Type ℓ'} {R : (x : A) → B x → Type ℓ''}
  → ((x : A) → Σ[ y ∈ B x ] R x y)
  → Σ[ f ∈ ((x : A) → B x) ] ((x : A) → R x (f x))
ac g = (λ x → fst (g x)) , (λ x → snd (g x))

Σ-ass : {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''}
  → Σ[ x ∈ A ] (Σ[ y ∈ B x ] C x y) → Σ[ xy ∈ Σ[ x ∈ A ] (B x) ] C (fst xy) (snd xy)
Σ-ass (x , y , z) = (x , y) , z
