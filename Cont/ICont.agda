module ICont where

private variable
  I : Set
  X Y : I → Set

infix  0 _◃_
record ICont (I : Set) : Set₁ where
  constructor _◃_
  field
    S : Set
    P : I → S → Set

private variable
  SP TQ : ICont I

record ContHom (SP TQ : ICont I) : Set where
  constructor _◃_
  open ICont SP
  open ICont TQ renaming (S to T; P to Q)
  field
    f : S → T
    g : (i : I) (s : S) → Q i (f s) → P i s
  
record ⟦_⟧ (SP : ICont I) (X : I → Set) : Set where
  constructor _,_
  open ICont SP
  field
    s : S
    k : (i : I) → P i s → X i

⟦_⟧₁ : (SP : ICont I)
  → ((i : I) → X i → Y i)
  → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ f (s , k) = s , λ i p → f i (k i p)

⟦_⟧Hom : (fg : ContHom SP TQ)
  → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ f ◃ g ⟧Hom (s , k) = f s , λ i p → k i (g i s p)
