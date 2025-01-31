{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

data ℤ : Set where
  zero : ℤ
  suc : ℤ → ℤ
  prd : ℤ → ℤ
  ps  : {x : ℤ} → prd (suc x) ≡ x
  sp  : {x : ℤ} → suc (prd x) ≡ x
  uip : {x y : ℤ} {p q : x ≡ y} → p ≡ q

- : ℤ → ℤ
- zero = zero
- (suc x) = prd (- x)
- (prd x) = suc (- x)
- (ps {x} i) = sp { - x} i
- (sp {x} i) = ps { - x} i
- (uip {x} {y} {p} {q} i j)
  = uip { - x} { - y} {λ k → - (p k)} {λ k → - (q k)} i j

_+_ : ℤ → ℤ → ℤ
zero + n = n
suc m + n = suc (m + n)
prd m + n = prd (m + n)
ps {x} i + n = ps {x + n} i
sp {x} i + n = sp {x + n} i
uip {x} {y} {p} {q} i j + n
  = uip {x + n} {y + n} {λ k → p k + n} {λ k → q k + n} i j
