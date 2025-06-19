module Data.W-type where
  
data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (B a → W A B) → W A B

rec : ∀ {A B} (P : W A B → Set)
  → ((a : A) (f : B a → W A B) → ((b : B a) → P (f b)) → P (sup a f))
  → (w : W A B) → P w
rec P α (sup a f) = α a f (λ b → rec P α (f b))
