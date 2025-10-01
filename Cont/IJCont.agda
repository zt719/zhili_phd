module Cont.ICont where

open import Data.Product

private variable
  I J K : Set
  X Y Z : I → Set

infix  0 _◃_

record IJCont (I J : Set) : Set₁ where
  constructor _◃_
  field
    S : J → Set
    P : (j : J) → S j → I → Set

private variable
  SP TQ : IJCont I J

record IJContHom (SP TQ : IJCont I J) : Set where
  constructor _◃_
  open IJCont SP
  open IJCont TQ renaming (S to T; P to Q)
  field
    f : (j : J) → S j → T j
    g : (j : J) (s : S j) (i : I) → Q j (f j s) i → P j s i

record ⟦_⟧ (SP : IJCont I J) (X : I → Set) (j : J) : Set where
  constructor _,_
  open IJCont SP
  field
    s : S j
    k : (i : I) → P j s i → X i

⟦_⟧₁ : (SP : IJCont I J)
  → ((i : I) → X i → Y i)
  → (j : J) → ⟦ SP ⟧ X j → ⟦ SP ⟧ Y j
⟦ SP ⟧₁ f j (s , k) = s , λ i p → f i (k i p)

⟦_⟧Hom : (fg : IJContHom SP TQ)
  → (j : J) → ⟦ SP ⟧ X j → ⟦ TQ ⟧ X j
⟦ f ◃ g ⟧Hom j (s , k) = f j s , λ i p → k i (g j s i p)

_∘_ : IJCont J K → IJCont I J → IJCont I K
(T ◃ Q) ∘ (S ◃ P)
  = (λ k → Σ[ t ∈ T k ] ((j : _) → Q k t j → S j))
  ◃ (λ k (t , f) i → Σ[ j ∈ _ ] Σ[ q ∈ Q k t j ] P j (f j q) i) 

{-
I J K : Set
S : J → Set
P : I → (j : J) → S j → Set
T : K → Set
Q : J → (j : K) → T j → Set

  ⟦ T ◃ Q ⟧ (⟦ S ◃ P ⟧ X) k
= Σ[ t ∈ T k ] ((j : J) → Q k t j → ⟦ S ◃ P ⟧ X i)
= Σ[ t ∈ T k ] ((j : J) → Q k t j → Σ[ s ∈ S j ] ((i : I) → P j s i → X i))
≃ Σ[ t ∈ T k ] Σ[ f ∈ (j : J) → Q k t j → S j ] ((j : J) (q : Q k t j) (i : I) → P j (f j q) i → X i)
≃ Σ[ (t , f) ∈ (T k × (j : J) → Q k t j → S j ] ((j : J) (q : Q k t j) (i : I) → P j (f j q) i → X i)
≃ Σ[ (t , f) ∈ (T k × (j : J) → Q k t j → S j ] ((i : I) (j : J) (q : Q k t j) → P j (f j q) i → X i)
≃ Σ[ (t , f) ∈ (T k × (j : J) → Q k t j → S j ] ((i : I) → Σ[ j ∈ J ] Σ[ q ∈ Q k t j ] P j (f j q) i → X i)
= ⟦ (λ k → Σ[ t ∈ T k ] ((j : J) → Q k t j → S j)) ◃ (λ k (t , f) i → Σ[ j ∈ J ] Σ[ q ∈ Q k t j ] P j (f j q) i) ⟧ k
-}

open import Data.Unit

ICont : Set → Set₁
ICont I = IJCont I ⊤

JCont : Set → Set₁
JCont J = IJCont ⊤ J

Cont : Set₁
Cont = IJCont ⊤ ⊤

{-
open import Data.Nat
open import Data.Fin

data List (X : Set) : Set where
  [] : List X
  _∷_ : X → List X → List X

ListCont : Cont
ListCont = (λ{ tt → ℕ }) ◃ λ{ tt n tt → Fin n }

List' : Set → Set
List' X = ⟦ ListCont ⟧ (λ { tt → X }) tt

data Vec (X : Set) : ℕ → Set where
  [] : Vec X 0
  _∷_ : ∀ {n} → X → Vec X n → Vec X (suc n)

tail : {X : Set} {n : ℕ} → Vec X (suc n) → Vec X n
tail (x ∷ xs) = xs

VecJCont : JCont ℕ
VecJCont = Fin ◃ λ{ n i tt → Fin n }

JContHom = IJContHom {I = ⊤}

tailHom : JContHom VecJCont VecJCont
tailHom = (λ{ (suc n) i → i }) ◃ λ{ (suc n) s tt x → s }

-}
