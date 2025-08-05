{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

data S¹ : Type where
  base : S¹
  loop : base ≡ base

data S² : Type where
  base : S²
  surf : refl {x = base} ≡ refl

data T² : Type where
  point : T²
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

t2c : T² → S¹ × S¹
t2c point = base , base
t2c (line1 i) = loop i , base
t2c (line2 i) = base , loop i
t2c (square i j) = loop i , loop j

c2t : S¹ × S¹ → T²
c2t (base , base) = point
c2t (base , loop i) = line2 i
c2t (loop i , base) = line1 i
c2t (loop i , loop j) = square i j

fromto : ∀ t → c2t (t2c t) ≡ t
fromto point = refl
fromto (line1 i) = refl
fromto (line2 i) = refl
fromto (square i j) = refl
