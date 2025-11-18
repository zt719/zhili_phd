variable X : Set

data LList (X : Set) : Set where
  []  : LList X
  _∷_ : X → LList (LList X) → LList X

open import Data.Nat

variable n : ℕ

data Foo (X : Set) : ℕ → Set where
  item : X → Foo X zero
  [] : Foo X (suc n)
  _∷_ : Foo X n → Foo X (suc (suc n)) → Foo X (suc n)

{- is this true ? -}
indLList : (P : (X : Set) → LList X → Set)
  → (pnil : (X : Set) → P X [])
  → (pcons : (X : Set) (x : X) (xs : LList (LList X)) → P (LList X) xs → P X (x ∷ xs))
  → (X : Set) (xs : LList X) → P X xs
indLList P pnil pcons X [] = pnil X
indLList P pnil pcons X (x ∷ xs) = pcons X x xs (indLList P pnil pcons (LList X) xs)

power : ℕ → Set → Set
power zero X = X
power (suc n) X = LList (power n X)

to : (n : ℕ) → power n X → Foo X n
to zero x = item x
to (suc n) x = {!!}
