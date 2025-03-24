{-# OPTIONS --type-in-type #-}

open import Data.Unit
open import Data.Product

data Ty : Set where
  ∘ : Ty
  _⇒_ : Ty → Ty → Ty

private variable A B C : Ty

⟦_⟧T : Ty → Set
⟦ ∘ ⟧T = Set
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

record Cat (Obj : Set) : Set where
  field
    Hom : Obj → Obj → Set
    id : ∀ {X} → Hom X X
    comp : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
open Cat    

record Func {X Y : Set} (C : Cat X) (D : Cat Y) (F : X → Y) : Set where
  field
    fmap : ∀ {X Y} → Hom C X Y → Hom D (F X) (F Y)

record Nat {X Y : Set}(C : Cat X)(D : Cat Y)(F G : X → Y)
           (FF : Func C D F)(GG : Func C D G) : Set where
  field
    η : ∀ X → Hom D (F X) (G X)

⟦_⟧F : (A : Ty) → ⟦ A ⟧T → Set
⟦_⟧C : (A : Ty) → Cat (Σ ⟦ A ⟧T ⟦ A ⟧F)

⟦ ∘ ⟧F X = ⊤
⟦ A ⇒ B ⟧F H = Σ[ HH ∈ ((F : ⟦ A ⟧T) → ⟦ A ⟧F F → ⟦ B ⟧F (H F)) ]
               Func ⟦ A ⟧C ⟦ B ⟧C (λ (F , FF) → H F , HH F FF)

⟦ ∘ ⟧C = record
  { Hom = λ (X , _) (Y , _) → X → Y
  ; id = λ x → x
  ; comp = λ f g x → f (g x)
  }

⟦ A ⇒ B ⟧C = record
  { Hom = λ (F , FF , FFF) (G , GG , GGG)
    → Nat ⟦ A ⟧C ⟦ B ⟧C (λ (X , XX) → F X , FF X XX) (λ (X , XX) → G X , GG X XX) FFF GGG

  ; id = record { η = λ X → id ⟦ B ⟧C }
  ; comp = λ{ record { η = η₁ } record { η = η₂ }
         → record { η = λ X → comp ⟦ B ⟧C (η₁ X) (η₂ X) } }
  }

infixl 5 _▹_
data Con : Set where
  ∙   : Con
  _▹_ : Con → Ty → Con

private variable Γ Δ : Con

data Var : Con → Ty → Set where
  vz : Var (Γ ▹ A) A
  vs : Var Γ A → Var (Γ ▹ B) A

private variable x y : Var Γ A

data Nf : Con → Ty → Set

record Ne (Γ : Con) (B : Ty) : Set

data Sp : Con → Ty → Ty → Set

data Nf where
  ne  : Ne Γ ∘ → Nf Γ ∘
  lam : Nf (Γ ▹ A) B → Nf Γ (A ⇒ B)

record Ne Γ B where
  inductive
  field
    S : Set
    P : S → Var Γ A → Set
    R : (s : S) (x : Var Γ A) (p : P s x) → Sp Γ A B

data Sp where
  ε   : Sp Γ A A
  _,_ : Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C

HCont : Ty → Set
HCont A = Nf ∙ A

{- Semantics -}

⟦_⟧Con : Con → Set
⟦ ∙ ⟧Con = ⊤
⟦ Γ ▹ A ⟧Con = ⟦ Γ ⟧Con × ⟦ A ⟧T

⟦_⟧v : Var Γ A → ⟦ Γ ⟧Con → ⟦ A ⟧T
⟦ vz ⟧v (γ , a) = a
⟦ vs x ⟧v (γ , a) = ⟦ x ⟧v γ

⟦_⟧nf : Nf Γ A → ⟦ Γ ⟧Con → ⟦ A ⟧T
⟦_⟧ne : Ne Γ ∘ → ⟦ Γ ⟧Con → Set
⟦_⟧sp : Sp Γ A B → ⟦ Γ ⟧Con → ⟦ A ⟧T → ⟦ B ⟧T

⟦ ne x ⟧nf γ = ⟦ x ⟧ne γ
⟦ lam x ⟧nf γ a = ⟦ x ⟧nf (γ , a)

⟦_⟧ne {Γ} record { S = S ; P = P ; R = R } γ =
  Σ[ s ∈ S ] ({A : Ty} (x : Var Γ A) (p : P s x) → ⟦ R s x p ⟧sp γ (⟦ x ⟧v γ))

⟦ ε ⟧sp γ a = a
⟦ n , ns ⟧sp γ f = ⟦ ns ⟧sp γ (f (⟦ n ⟧nf γ))

⟦_⟧ : HCont A → ⟦ A ⟧T
⟦ x ⟧ = ⟦ x ⟧nf tt

{- More -}


{-
nf2hf : (H : Nf Γ A) (γ : ⟦ Γ ⟧Con)→ ⟦ A ⟧F (⟦ H ⟧nf γ)
nf2hf (ne x) γ = tt
nf2hf (lam H) γ = (λ F x → nf2hf H (γ , F)) , record { fmap =
  λ {(F , FF)} {(G , GG)} f → {!!}
  }

nc2nf : (H : HCont A) → ⟦ A ⟧F ⟦ H ⟧hcont
nc2nf H = nf2hf H tt
-}
