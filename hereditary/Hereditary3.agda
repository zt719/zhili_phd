module Hereditary3 where

{- Syntax -}

infixr 4 _⇒_
data Ty : Set where
  ∘ : Ty
  _⇒_ : Ty → Ty → Ty

data Tel : Set
data CTy : Set

infixl 4 _◃_
data Tel where
  ∙   : Tel
  _◃_ : CTy → Tel → Tel

private variable Γ Δ : Tel

infix  1 _⇒∘
data CTy where
  _⇒∘ : Tel → CTy

dom : CTy → Tel
dom (Γ ⇒∘) = Γ

private variable A B C : CTy

uncurry : Ty → CTy
uncurry ∘ = ∙ ⇒∘
uncurry (A ⇒ B) = (uncurry A ◃ dom (uncurry B)) ⇒∘

curry : CTy → Ty
curry (∙ ⇒∘) = ∘
curry (A ◃ Γ ⇒∘) = curry A ⇒ curry (Γ ⇒∘)

longTy : Ty
longTy = ((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘) ⇒ ∘ ⇒ ∘

data Var : Tel → CTy → Set where
  vz : Var (A ◃ Γ) A
  vs : Var Γ A → Var (B ◃ Γ) A

private variable x y z : Var Γ A

data Nf : Tel → CTy → Set

data Ne : Tel → Set

data Sp : Tel → Tel → Set

data Nf where
  lam : Nf (A ◃ Γ) (Δ ⇒∘) → Nf Γ (A ◃ Δ ⇒∘)
  ne  : Ne Γ → Nf Γ (∙ ⇒∘)

data Ne where
  _,_ : Var Γ (Δ ⇒∘) → Sp Γ Δ → Ne Γ

data Sp where
  ε   : Sp Γ ∙
  _,_ : Nf Γ A → Sp Γ Δ → Sp Γ (A ◃ Δ)

{-
-- λf.λz.f (f z)
exnf : Nf ∙ ((∘ ⇒ ∘) ⇒ (∘ ⇒ ∘))
exnf = lam (lam (ne (vs vz , (ne (vs vz , (ne (vz , ε) , ε)) , ε))))

-}

exnf : Nf ∙ (uncurry ((∘ ⇒ ∘) ⇒ (∘ ⇒ ∘)))
exnf = lam (lam (ne (vs vz , (ne (vs vz , (ne (vz , ε) , ε)) , ε))))

{-
appSp : Sp Γ A → Nf Γ B → Sp Γ (spTy A B)
appSp ε u = u , ε
appSp (t , ts) u = t , appSp ts u
-}

{- snoc -}
_▹_ : Tel → CTy → Tel
∙ ▹ A = A ◃ ∙
(A ◃ Γ) ▹ B = A ◃ (Γ ▹ B)

appSp : Sp Γ Δ → Nf Γ A → Sp Γ (Δ ▹ A)
appSp ε u = u , ε
appSp (n , ns) u = n , appSp ns u
