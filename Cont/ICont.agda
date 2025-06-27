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
    P : I → S → Set

private variable
  SP TQ : ICont I

record IContHom (SP TQ : ICont I) : Set where
  constructor _◃_
  open ICont SP
  open ICont TQ renaming (S to T; P to Q)
  field
    f : S → T
    g : (i : I) (s : S) → Q i (f s) → P i s
  
record ⟦_⟧₀ (SP : ICont I) (X : I → Set) : Set where
  constructor _,_
  open ICont SP
  field
    s : S
    k : (i : I) → P i s → X i

⟦_⟧₁ : (SP : ICont I)
  → ((i : I) → X i → Y i)
  → ⟦ SP ⟧₀ X → ⟦ SP ⟧₀ Y
⟦ SP ⟧₁ f (s , k) = s , λ i p → f i (k i p)

⟦_⟧Hom : (fg : IContHom SP TQ)
  → ⟦ SP ⟧₀ X → ⟦ TQ ⟧₀ X
⟦ f ◃ g ⟧Hom (s , k) = f s , λ i p → k i (g i s p)

_→*_ : (I → Set) → (I → Set) → Set
X →* Y = (i : _) → X i → Y i

id* : X →* X
id* i x = x

_∘*_ : Y →* Z → X →* Y → X →* Z
(f ∘* g) i x = f i (g i x)

record IFunc (I : Set) : Set₁ where
  constructor _,_
  field
    F₀ : (I → Set) → Set
    F₁ : ((i : I) → X i → Y i) → F₀ X → F₀ Y

_⇒_ : IFunc I → IFunc I → Set₁
(F , _) ⇒ (G , _) = (X : _ → Set) → F X → G X

⟦_⟧ : ICont I → IFunc I
⟦ SP ⟧ = ⟦ SP ⟧₀ , ⟦ SP ⟧₁
