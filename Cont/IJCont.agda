module IJCont where

open import Data.Product

private variable
  I J K : Set
  X Y : I → Set

infix  0 _◃_
record IJCont (I J : Set) : Set₁ where
  constructor _◃_
  field
    S : J → Set
    P : I → (j : J) → S j → Set

private variable
  SP TQ : IJCont I J

record IJContHom (SP TQ : IJCont I J) : Set where
  constructor _◃_
  open IJCont SP
  open IJCont TQ renaming (S to T; P to Q)
  field
    f : (j : J) → S j → T j
    g : (i : I) (j : J) (s : S j) → Q i j (f j s) → P i j s

record ⟦_⟧ (SP : IJCont I J) (X : I → Set) (j : J) : Set where
  constructor _,_
  open IJCont SP
  field
    s : S j
    k : (i : I) → P i j s → X i

⟦_⟧₁ : (SP : IJCont I J)
  → ((i : I) → X i → Y i)
  → (j : J) → ⟦ SP ⟧ X j → ⟦ SP ⟧ Y j
⟦ SP ⟧₁ f j (s , k) = s , λ i p → f i (k i p)

⟦_⟧Hom : (fg : IJContHom SP TQ)
  → (j : J) → ⟦ SP ⟧ X j → ⟦ TQ ⟧ X j
⟦ f ◃ g ⟧Hom j (s , k) = f j s , λ i p → k i (g i j s p)

_∘_ : IJCont J K → IJCont I J → IJCont I K
(T ◃ Q) ∘ (S ◃ P)
  = (λ k → Σ[ t ∈ T k ] ((j : _) → Q j k t → S j))
  ◃ (λ i k (t , f) → Σ[ j ∈ _ ] Σ[ q ∈ Q j k t ] P i j (f j q))

{-
I J K : Set
S : J → Set
P : I → (j : J) → S j → Set
T : K → Set
Q : J → (j : K) → T j → Set

  ⟦ T ◃ Q ⟧ (⟦ S ◃ P ⟧ X) k
= Σ[ t ∈ T k ] ((j : J) → Q j k t → ⟦ S ◃ P ⟧ X i)
= Σ[ t ∈ T k ] ((j : J) → Q j k t → Σ[ s ∈ S j ] ((i : I) → P i j s → X i))
≃ Σ[ t ∈ T k ] Σ[ f ∈ (j : J) → Q j k t → S j ] ((j : J) (q : Q j k t) (i : I) → P i j (f j q) → X i)
≃ Σ[ (t , f) ∈ (T k × (j : J) → Q j k t → S j ] ((j : J) (q : Q j k t) (i : I) → P i j (f j q) → X i)
≃ Σ[ (t , f) ∈ (T k × (j : J) → Q j k t → S j ] ((i : I) (j : J) (q : Q j k t) → P i j (f j q) → X i)
≃ Σ[ (t , f) ∈ (T k × (j : J) → Q j k t → S j ] ((i : I) → Σ[ j ∈ J ] Σ[ q ∈ Q j k t ] P i j (f j q) → X i)
= ?  
-}
