{-# OPTIONS --guardedness --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Codata.Stream
open Stream

φ : {A : Set} → (ℕ → A) → Stream A
head (φ f) = f zero
tail (φ f) = φ (λ n → f (suc n))

ψ : {A : Set} → Stream A → ℕ → A
ψ as zero = head as
ψ as (suc n) = ψ (tail as) n

retr : {A : Set} (f : ℕ → A) → ψ (φ f) ≡ f
retr f i zero = f zero
retr f i (suc n) = retr (λ n → f (suc n)) i n

sec : {A : Set} (as : Stream A) → φ (ψ as) ≡ as
head (sec as i) = head as
tail (sec as i) = sec (tail as) i

thePath : {A : Set} → (ℕ → A) ≡ Stream A
thePath = isoToPath (iso φ ψ sec retr)
