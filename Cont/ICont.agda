module ICont where

open import Data.Product

private variable
  I : Set
  X Y Z : I → Set

infix  0 _◃_

record ICont (I : Set) : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → I → Set

private variable
  SP TQ : ICont I

record IContHom (SP TQ : ICont I) : Set where
  constructor _◃_
  open ICont SP
  open ICont TQ renaming (S to T; P to Q)
  field
    f : S → T
    g : (s : S) (i : I) → Q (f s) i → P s i
  
record ⟦_⟧₀ (SP : ICont I) (X : I → Set) : Set where
  constructor _,_
  open ICont SP
  field
    s : S
    k : (i : I) → P s i → X i

⟦_⟧₁ : (SP : ICont I)
  → ((i : I) → X i → Y i)
  → ⟦ SP ⟧₀ X → ⟦ SP ⟧₀ Y
⟦ SP ⟧₁ f (s , k) = s , λ i p → f i (k i p)

⟦_⟧Hom : (fg : IContHom SP TQ)
  → ⟦ SP ⟧₀ X → ⟦ TQ ⟧₀ X
⟦ f ◃ g ⟧Hom (s , k) = f s , λ i p → k i (g s i p)

_→*_ : (I → Set) → (I → Set) → Set
X →* Y = (i : _) → X i → Y i

id* : X →* X
id* i x = x

_∘*_ : Y →* Z → X →* Y → X →* Z
(f ∘* g) i x = f i (g i x)

IFunc : Set → Set₁
IFunc I
  = Σ[ F ∈ ((I → Set) → Set) ]
  ({X Y : I → Set} → ((i : I) → X i → Y i) → F X → F Y)

_⇒_ : IFunc I → IFunc I → Set₁
(F , _) ⇒ (G , _) = (X : _ → Set) → F X → G X

⟦_⟧ : ICont I → IFunc I
⟦ SP ⟧ = ⟦ SP ⟧₀ , ⟦ SP ⟧₁

