module IJCont where

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

record ⟦_⟧₀ (SP : IJCont I J) (X : I → Set) (j : J) : Set where
  constructor _,_
  open IJCont SP
  field
    s : S j
    k : (i : I) → P j s i → X i

⟦_⟧₁ : (SP : IJCont I J)
  → ((i : I) → X i → Y i)
  → (j : J) → ⟦ SP ⟧₀ X j → ⟦ SP ⟧₀ Y j
⟦ SP ⟧₁ f j (s , k) = s , λ i p → f i (k i p)

⟦_⟧Hom : (fg : IJContHom SP TQ)
  → (j : J) → ⟦ SP ⟧₀ X j → ⟦ TQ ⟧₀ X j
⟦ f ◃ g ⟧Hom j (s , k) = f j s , λ i p → k i (g j s i p)

IJFunc : Set → Set → Set₁
IJFunc I J
  = Σ[ F ∈ ((I → Set) → J → Set) ]
  ({X Y : I → Set} → ((i : I) → X i → Y i) → (j : J) → F X j → F Y j)

_→*_ : (I → Set) → (I → Set) → Set
X →* Y = (i : _) → X i → Y i

id* : X →* X
id* i x = x

_∘*_ : Y →* Z → X →* Y → X →* Z
(f ∘* g) i x = f i (g i x)

⟦_⟧ : IJCont I J → IJFunc I J
⟦ SP ⟧ = ⟦ SP ⟧₀ , ⟦ SP ⟧₁

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

  ⟦ T ◃ Q ⟧₀ (⟦ S ◃ P ⟧₀ X) k
= Σ[ t ∈ T k ] ((j : J) → Q k t j → ⟦ S ◃ P ⟧₀ X i)
= Σ[ t ∈ T k ] ((j : J) → Q k t j → Σ[ s ∈ S j ] ((i : I) → P j s i → X i))
≃ Σ[ t ∈ T k ] Σ[ f ∈ (j : J) → Q k t j → S j ] ((j : J) (q : Q k t j) (i : I) → P j (f j q) i → X i)
≃ Σ[ (t , f) ∈ (T k × (j : J) → Q k t j → S j ] ((j : J) (q : Q k t j) (i : I) → P j (f j q) i → X i)
≃ Σ[ (t , f) ∈ (T k × (j : J) → Q k t j → S j ] ((i : I) (j : J) (q : Q k t j) → P j (f j q) i → X i)
≃ Σ[ (t , f) ∈ (T k × (j : J) → Q k t j → S j ] ((i : I) → Σ[ j ∈ J ] Σ[ q ∈ Q k t j ] P j (f j q) i → X i)
= ⟦ (λ k → Σ[ t ∈ T k ] ((j : J) → Q k t j → S j)) ◃ (λ k (t , f) i → Σ[ j ∈ J ] Σ[ q ∈ Q k t j ] P j (f j q) i) ⟧₀ k
-}
