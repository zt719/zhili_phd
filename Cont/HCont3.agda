{-# OPTIONS --type-in-type #-}

module Cont.HCont3 where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

{- Syntax -}

infixr 20 _⇒_
data Ty : Set where
  ∘ : Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

infixl 5 _▹_
data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

variable Γ Δ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

variable x y : Var Γ A

data HCont-NF : Con → Ty → Set

-- record HCont-NE (Γ : Con) (B : Ty) : Set
data HCont-NE : Con → Ty → Set

data HCont-SP : Con → Ty → Ty → Set

data HCont-NF where
  lam : HCont-NF (Γ ▹ A) B → HCont-NF Γ (A ⇒ B)
  ne  : HCont-NE Γ ∘ → HCont-NF Γ ∘

{-
record HCont-NE Γ B where
  inductive
  field
    S : Set
    P : S → Var Γ A → Set
    R : (s : S) (x : Var Γ A) (p : P s x) → HCont-SP Γ A B
-}

data HCont-NE where
  mkNE : (Σ[ S ∈ Set ] Σ[ P ∈ (S → Var Γ A → Set) ]
    ((s : S) (x : Var Γ A) (p : P s x) → HCont-SP Γ A B))
    → HCont-NE Γ B

data HCont-SP where
  ε   : HCont-SP Γ A A
  _,_ : HCont-NF Γ A → HCont-SP Γ B C → HCont-SP Γ (A ⇒ B) C

HCont : Ty → Set
HCont A = HCont-NF ∙ A

H : (Set → Set) → (Set → Set)
H F A = A × F (F A)

{-
BCont : HCont ((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘)
BCont = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ ∘ ⇒ ∘ ▹ ∘

  NF-A : HCont-NF Γ₀ ∘
  NF-A = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : S → Var Γ₀ A → Set
    P tt vz = ⊤
    P tt (vs vz) = ⊥

    R : (s : S) (x : Var Γ₀ A) → P s x → HCont-SP Γ₀ A ∘
    R tt vz tt = ε
    R tt (vs vz) ()
  
  NF-FA : HCont-NF Γ₀ ∘
  NF-FA = ne (record { S = S ; P = P ; R = R })
    where
    S : Set
    S = ⊤

    P : S → Var Γ₀ A → Set
    P tt vz = ⊥
    P tt (vs vz) = ⊤

    R : (s : S) (x : Var Γ₀ A) → P s x → HCont-SP Γ₀ A ∘
    R tt vz ()
    R tt (vs vz) tt = NF-A , ε

  
  S : Set
  S = ⊤

  P : S → Var Γ₀ A → Set
  P tt vz = ⊤
  P tt (vs vz) = ⊤

  R : (s : S) (x : Var Γ₀ A) → P s x → HCont-SP Γ₀ A ∘
  R tt vz tt = ε
  R tt (vs vz) tt = NF-FA , ε

----

open import Cont.Cont

HCont→Cont : HCont (∘ ⇒ ∘) → Cont
HCont→Cont (lam (ne record { S = S ; P = P ; R = R })) = S ◃ λ s → P s vz

Cont→HCont : Cont → HCont (∘ ⇒ ∘)
Cont→HCont (S ◃ P) = lam (ne (record { S = S ; P = λ{ s vz → P s } ; R = λ{ s vz p → ε } }))

----
-}

⟦_⟧T : Ty → Set
⟦ ∘ ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Con → Set
⟦ ∙ ⟧C = ⊤
⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ vz ⟧v (γ , a) = a
⟦ vs x ⟧v (γ , a) = ⟦ x ⟧v γ

⟦_⟧nf : HCont-NF Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦_⟧ne : HCont-NE Γ ∘ → ⟦ Γ ⟧C → Set
⟦_⟧sp : HCont-SP Γ A B → ⟦ Γ ⟧C → ⟦ A ⟧T → ⟦ B ⟧T

⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)
⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ

⟦_⟧ne {Γ} (mkNE (S , P , R)) γ = 
  Σ[ s ∈ S ] ((x : Var Γ _) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))

⟦ ε ⟧sp γ a = a
⟦ n , ns ⟧sp γ f = ⟦ ns ⟧sp γ (f (⟦ n ⟧nf γ))

⟦_⟧hcont : HCont A → ⟦ A ⟧T
⟦ x ⟧hcont = ⟦ x ⟧nf tt

{-
{-
B-HCont : (Set → Set) → Set → Set
B-HCont = ⟦ BCont ⟧hcont

{-
= ⟦ lam (lam (ne (record { S = S ; P = P ; R = R }))) ⟧hcont
= ⟦ lam (lam (ne (record { S = S ; P = P ; R = R }))) ⟧nf tt
= λ F → ⟦ lam (ne (record { S = S ; P = P ; R = R })) ⟧nf (tt , F)
= λ F X → ⟦ ne (record { S = S ; P = P ; R = R }) ⟧nf (tt , F , X)
= λ F X → ⟦ record { S = S ; P = P ; R = R } ⟧ne (tt , F , X)
= λ F X → ⟦ record { S = S ; P = P ; R = R } ⟧ne (tt , F , A)
= λ F X → Σ[ s ∈ S ] ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))   # γ = tt , F , X

  Σ[ s ∈ S ] ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))
= ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))                # S = ⊤
= ⟦ R tt vz tt ⟧sp γ (⟦ vz ⟧v γ) × ⟦ R tt one tt ⟧sp γ (⟦ one ⟧v γ))  # P tt vz = ⊤ , P tt one = ⊤
= ⟦ ε ⟧sp γ (⟦ vz ⟧v γ) × ⟦ ne FFA , ε ⟧sp γ (⟦ one ⟧v γ)               # R ...
= ⟦ vz ⟧v γ × ⟦ ε ⟧sp γ (⟦ one ⟧v γ (⟦ ne NE-FA ⟧nf γ))
= X × ⟦ one ⟧v γ (⟦ ne NE-FA ⟧nf γ)
= X × F (⟦ ne NE-FA ⟧nf γ)
= X × F (⟦ NE-FA ⟧ne γ)

  ⟦ NE-FA ⟧ne γ
= ⟦ record { S = S ; P = P ; R = R } ⟧ne γ
= Σ[ s ∈ S ] ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))   # by definition of S , P , R
= ⟦ ne NE-A , ε ⟧sp γ (⟦ one ⟧v γ)
= ⟦ ε ⟧sp γ (⟦ one ⟧v γ (⟦ ne NE-A ⟧nf γ))
= ⟦ one ⟧v γ (⟦ ne NE-A ⟧nf γ)
= F (⟦ ne NE-A ⟧nf γ)

  ⟦ ne NE-A ⟧nf γ
= ⟦ record { S = S ; P = P ; R = R } ⟧ne γ
= Σ[ s ∈ S ] ((x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))   # by definition of S , P , R
= ⟦ ε ⟧γ (⟦ vz ⟧v γ)
= ⟦ vz ⟧v γ
= A
-}


---

WOW : ((Set → Set) → Set → Set) → (Set → Set) → Set → Set
WOW H F X = H F X

WOW-HCont : HCont (((∘ ⇒ ∘) ⇒ ∘ ⇒ ∘) ⇒ (∘ ⇒ ∘) ⇒ ∘ ⇒ ∘)
WOW-HCont = lam (lam (lam (ne (record { S = S ; P = P ; R = R }))))
  where
  Γ₀ : Con
  Γ₀ = ∙ ▹ (∘ ⇒ ∘) ⇒ ∘ ⇒ ∘ ▹ ∘ ⇒ ∘ ▹ ∘
  
  S : Set
  S = ⊤

  P : S → Var Γ₀ A → Set
  P tt vz = ⊥
  P tt (vs vz) = ⊥
  P tt (vs (vs vz)) = ⊤

  R : (s : S) (x : Var Γ₀ A) → P s x → HCont-SP Γ₀ A
  R tt (vs (vs vz)) tt = F-NF , X-NF , ε
    where
    F-NF : HCont-NF Γ₀ (∘ ⇒ ∘)
    F-NF = lam (ne (record { S = F-S ; P = F-P ; R = F-R }))
      where
      F-S : Set
      F-S = ⊤

      F-P : F-S → Var (Γ₀ ▹ ∘) A → Set
      F-P tt vz = ⊥
      F-P tt (vs vz) = ⊥
      F-P tt (vs (vs vz)) = ⊤
      F-P tt (vs (vs (vs vz))) = ⊥

      F-R : (s : F-S) (x : Var (Γ₀ ▹ ∘) A) → F-P s x → HCont-SP (Γ₀ ▹ ∘) A
      F-R tt (vs (vs vz)) tt = Y-NF , ε
        where
        Y-NF : HCont-NF (Γ₀ ▹ ∘) ∘
        Y-NF = ne (record { S = Y-S ; P = Y-P ; R = Y-R })
          where
          Y-S : Set
          Y-S = ⊤

          Y-P : Y-S → Var (Γ₀ ▹ ∘) A → Set
          Y-P tt vz = ⊤
          Y-P tt (vs x) = ⊥

          Y-R : (s : Y-S) (x : Var (Γ₀ ▹ ∘) A) → Y-P s x → HCont-SP (Γ₀ ▹ ∘) A
          Y-R tt vz tt = ε
      F-R tt (vs (vs (vs vz))) ()

    
    X-NF : HCont-NF Γ₀ ∘
    X-NF = ne (record { S = X-S ; P = X-P ; R = X-R })
      where
      X-S : Set
      X-S = ⊤

      X-P : X-S → Var Γ₀ A → Set
      X-P tt vz = ⊤
      X-P tt (vs x) = ⊥

      X-R : (s : X-S) (x : Var Γ₀ A) → X-P s x → HCont-SP Γ₀ A
      X-R tt vz tt = ε
-}
-}

app : HCont-NF Γ (A ⇒ B) → HCont-NF (Γ ▹ A) B
app (lam x) = x

appSp : HCont-SP Γ A (B ⇒ C) → HCont-NF Γ B → HCont-SP Γ A C
appSp ε u = u , ε
appSp (n , ns) u = n , appSp ns u

-- Weakening
_-_ : (Γ : Con) → Var Γ A → Con
∙ - ()
(Γ ▹ A) - vz = Γ
(Γ ▹ A) - (vs x) = (Γ - x) ▹ A

wkv : (x : Var Γ A) → Var (Γ - x) B → Var Γ B
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

-- Variable Equality

open import Data.Bool
eq : Var Γ A → Var Γ B → Bool
eq vz vz = true
eq vz (vs y) = false
eq (vs x) vz = false
eq (vs x) (vs y) = true

nvar : Var Γ A → HCont-NF Γ A
ne2nf : HCont-NE Γ A → HCont-NF Γ A

nvar {Γ} {A} x =
  ne2nf (mkNE (S , P , R))
  where
  S : Set
  S = ⊤

  P : S → Var Γ A → Set
  P tt y with eq x y
  ... | false = ⊥
  ... | true = ⊤

  R : (s : S) (y : Var Γ A) → P s y → HCont-SP Γ A A
  R tt y p with eq x y
  R tt y tt | true = ε

ne2nf {Γ} {∘} x = ne x
ne2nf {Γ} {A ⇒ B} (mkNE (S , P , R)) =
  lam (ne2nf (mkNE (S , P' , R')))
  where
  P' : S → Var (Γ ▹ A) A → Set
  P' = {!!}

  R' : (s : S) (x : Var (Γ ▹ A) A) → P' s x → HCont-SP (Γ ▹ A) A B
  R' s x p = appSp {!!} (nvar vz)
