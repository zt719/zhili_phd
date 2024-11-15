{-# OPTIONS --type-in-type #-}

{- without dom, and appT has positivity problem -}

open import Data.Product
open import Data.Unit
open import Data.Empty

infixr 5 _⇒_
data Ty : Set where
  set : Ty
  _⇒_ : Ty → Ty → Ty
  
infixl 5 _▷_
data Con : Set where
  • : Con
  _▷_ : Con → Ty → Con

-- dom (A ⇒ B ⇒ set) = • ▷ A ▷ B
dom : Ty → Con
dom set = •
dom (A ⇒ B) = dom B ▷ A

variable A B C : Ty
variable Γ Δ : Con

-- test
module _(A B : Ty) where
  x = dom (A ⇒ B ⇒ set)

data Var : Con → Ty → Set where
  zero : Var (Γ ▷ A) A
  suc : Var Γ A → Var (Γ ▷ B) A

record HCont-Set (Γ : Con) : Set 
data HCont-NE (Γ : Con) : Ty → Set

-- HCont-NE Γ (A ⇒ B ⇒ set) = ε , HCont-NF Γ B , HCont-NF Γ A  

data HCont-NF : Con → Ty → Set where
  lam : HCont-NF (Γ ▷ A) B → HCont-NF Γ (A ⇒ B)
  ne : HCont-Set Γ → HCont-NF Γ set

record HCont-Set Γ  where
  inductive
  field
    S : Var Γ A → Set
    P : {x : Var Γ A}(s : S x) → Set
    R : {x : Var Γ A}{s : S x}(p : P s) → HCont-NE Γ A

data HCont-NE Γ where
  ε : HCont-NE Γ set
  _,_ : HCont-NF Γ A → HCont-NE Γ B → HCont-NE Γ (A ⇒ B)

HCont : Ty → Set
HCont A = HCont-NF • A

-- Semantics

⟦_⟧T : Ty → Set
⟦ set ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

⟦_⟧C : Con → Set
⟦ • ⟧C = ⊤
⟦ Γ ▷ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ zero ⟧v (_ , a) = a
⟦ suc x ⟧v (γ , _) = ⟦ x ⟧v γ

-- record ⟦_⟧set (DD : HCont-Set Γ)(γ : ⟦ Γ ⟧C) : Set
-- ⟦_⟧set : (DD : HCont-Set Γ)(γ : ⟦ Γ ⟧C) → Set
data ⟦_⟧ne : HCont-NE Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T → Set

⟦_⟧nf : HCont-NF Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
⟦ lam CC ⟧nf γ a = ⟦ CC ⟧nf (γ , a)
--⟦ ne DD ⟧nf γ = ⟦ DD ⟧set γ
⟦ ne {Γ = Γ} record { S = S ; P = P ; R = R } ⟧nf γ =
  Σ[ s ∈ ({A : Ty}(x : Var Γ A) → S x) ]
    ({A : Ty}{x : Var Γ A}{s : S x}(p : P s) → ⟦ R p ⟧ne γ (⟦ x ⟧v γ) )

{-
{!  Σ[ s ∈ ({A : Ty}(x : Var Γ A) → S x) ]
    ({A : Ty}{x : Var Γ A}{s : S x}(p : P s) → ⟦ R p ⟧ne γ (⟦ x ⟧v γ) )
!}
-}

{-
record ⟦_⟧set {Γ} CC γ where
  inductive
  open HCont-Set CC
  field
    s : (x : Var Γ A) → S x
    r : {x : Var Γ A}{s : S x}(p : P s) → ⟦ R p ⟧ne γ (⟦ x ⟧v γ)
-}
-- ⟦ R p ⟧ne γ (⟦ x ⟧v γ)

{-# NO_POSITIVITY_CHECK #-}
data ⟦_⟧ne where
  ε : {γ : ⟦ Γ ⟧C} → (X : Set) → ⟦ ε ⟧ne γ X
  _,_ : {γ : ⟦ Γ ⟧C}(CC : HCont-NF Γ A)(CC* : HCont-NE Γ B)
        (f : ⟦ A ⟧T → ⟦ B ⟧T) → ⟦ CC* ⟧ne γ (f (⟦ CC ⟧nf γ))
            → ⟦ CC , CC* ⟧ne γ f
{-



⟦ CC , CC* ⟧ne γ 
-}



{-
⟦ ε ⟧ne γ A = A
⟦ CC , CC* ⟧ne γ F = ⟦ CC* ⟧ne γ (F (⟦ CC ⟧nf γ))
-}

-- examples

H : (Set → Set) → (Set → Set)
H F A = A × F (F A)

{-
NE = neutral  x m n 
NF = normal   λ x y → ...

HCont-Set (Γ₀ = • ▷ (set ⇒ set) ▷ set)
   

-}




TT : Ty
TT = (set ⇒ set) ⇒ set ⇒ set

HC : HCont TT
HC = lam (lam (ne (record { S = S ; P = P ; R = R })))
  where Γ₀ : Con
        Γ₀ = • ▷ (set ⇒ set) ▷ set
        S : {A : Ty} → Var Γ₀ A → Set
        S zero = ⊤
        S (suc zero) = ⊤
        P : {A : Ty} {x : Var Γ₀ A} → S x → Set
        P {x = zero} tt = ⊤
        P {x = suc zero} tt = ⊤
        R-FA-S : {A : Ty} → Var Γ₀ A → Set
        R-FA-S zero = ⊤
        R-FA-S (suc zero) = ⊤
        R-FA-P :  {A : Ty} {x : Var Γ₀ A} → R-FA-S x → Set 
        R-FA-P {x = zero} tt = ⊤
        R-FA-P {x = suc zero} tt = ⊥
        R-FA-R :  {A : Ty} {x : Var Γ₀ A} {s : R-FA-S x} → R-FA-P s → HCont-NE Γ₀ A
        R-FA-R {x = zero} tt = ε
        R-FA-R {x = suc zero} ()
        R-FA-R {x = suc (suc ())} s
        R-FA : HCont-Set Γ₀
        R-FA = record { S = R-FA-S ; P = R-FA-P ; R = R-FA-R }            
        R-FFA-S : {A : Ty} → Var Γ₀ A → Set
        R-FFA-S zero = ⊤
        R-FFA-S (suc zero) = ⊤
        R-FFA-P :  {A : Ty} {x : Var Γ₀ A} → R-FFA-S x → Set 
        R-FFA-P {x = zero} tt = ⊥
        R-FFA-P {x = suc zero} tt = ⊤
        R-FFA-R :  {A : Ty} {x : Var Γ₀ A} {s : R-FFA-S x} → R-FFA-P s → HCont-NE Γ₀ A
        R-FFA-R {x = zero} ()
        R-FFA-R {x = suc zero} p = (ne R-FA) , ε
        R-FFA-R {x = suc (suc ())} s
        R-FFA : HCont-Set Γ₀
        R-FFA = record { S = R-FFA-S ; P = R-FFA-P ; R = R-FFA-R }  
        R : {A : Ty} {x : Var Γ₀ A} {s : S x} → P s → HCont-NE Γ₀ A
        R {x = zero} p = ε
        R {x = suc zero} p = (ne R-FFA) , ε
