{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level

Π : (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π A B = (a : A) → B a

infix 2 Π-syntax

Π-syntax : (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π-syntax = Π

syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B

module _ {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''} where

  choice :
    ((a : A) → Σ[ b ∈ B a ] C a b)
    → Σ[ f ∈ ((a : A) → B a) ] ((a : A) → C a (f a))
  choice g = (λ a → fst (g a)) , (λ a → snd (g a))

  curry :
    ((ab : Σ[ a ∈ A ] B a) → C (fst ab) (snd ab))
    → ((a : A) (b : B a) → C a b)
  curry g a b = g (a , b)

  Σ-ass :
    Σ[ a ∈ A ] (Σ[ b ∈ B a ] C a b)
    → Σ[ ab ∈ Σ[ a ∈ A ] (B a) ] C (fst ab) (snd ab)
  Σ-ass (a , b , c) = (a , b) , c


{-
record CMon : Type₁ where
  field
    O : Type
    e : O
    _*_ : O → O → O
    lunit : ∀ a → e * a ≡ a
    runit : ∀ a → a * e ≡ a
    ass   : ∀ a b c → a * (b * c) ≡ (a * b) * c
    com   : ∀ a b → a * b ≡ b * a
open CMon

record _⇒_ (M N : CMon) : Type where
  field
    O⇒ : M .O → N .O
    e⇒ : O⇒ (M .e) ≡ N .e
    *⇒ : ∀ a b → O⇒ (M ._*_ a b) ≡ N ._*_ (O⇒ a) (O⇒ b)
open _⇒_    

_⊕_ : CMon → CMon → CMon
(M ⊕ N) .O = M .O × N .O
(M ⊕ N) .e = M .e , N .e
(M ⊕ N) ._*_ (a , b) (a' , b') = M ._*_ a a' , N ._*_ b b'
(M ⊕ N) .lunit (a , b) i = M .lunit a i , N .lunit b i
(M ⊕ N) .runit (a , b) i = (M . runit a i) , (N .runit b i)
(M ⊕ N) .ass (a , b) (a' , b') (a'' , b'') i = (M .ass a a' a'' i) , N .ass b b' b'' i
(M ⊕ N) .com (a , b) (a' , b') i = (M .com a a' i) , (N .com b b' i)

π₁ : ∀ {M N} → (M ⊕ N) ⇒ M
π₁ .O⇒ (a , b) = a
π₁ .e⇒ = refl
π₁ .*⇒ a b = refl

π₂ : ∀ {M N} → (M ⊕ N) ⇒ N
π₂ .O⇒ (a , b) = b
π₂ .e⇒ = refl
π₂ .*⇒ a b = refl

i₁ : ∀ {M N} → M ⇒ (M ⊕ N)
(i₁ {N = N}) .O⇒ a = a , N .e
i₁ .e⇒ = refl
(i₁ {M} {N}) .*⇒ a b i = M ._*_ a b , N .lunit (N .e) (~ i)

i₂ : ∀ {M N} → N ⇒ (M ⊕ N)
(i₂ {M = M}) .O⇒ b = M .e , b
i₂ .e⇒ = refl
(i₂ {M} {N}) .*⇒ a b i = M .lunit (M .e) (~ i) , (N ._*_ a b)
-}

data ℕ : Set where
  zero : ℕ
  suc  :  ℕ → ℕ

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {n m : ℕ} → n ≤ m → suc n ≤ suc m

0≤1 : zero ≤ suc zero
0≤1 = z≤n

1≤2 : suc zero ≤ suc (suc zero)
1≤2 = s≤s 0≤1

2≤3 : suc (suc zero) ≤ suc (suc (suc zero))
2≤3 = s≤s 1≤2

---------

data _≤'_ : ℕ → ℕ → Set where
  n≤'n : {n : ℕ} → n ≤' n
  n≤'s : {n m : ℕ} → n ≤' m → n ≤' suc m

2≤'2 : suc (suc zero) ≤' suc (suc zero)
2≤'2 = n≤'n

2≤'3 : suc (suc zero) ≤' suc (suc (suc zero))
2≤'3 = n≤'s 2≤'2

_ : {n m : ℕ} → n ≤ m ≡ n ≤' m
_ = {!ℕ !}

ℕ NN ℕ₁ ℕ
