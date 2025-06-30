module Cont.2Cont where

open import Function.Base

record 1Cont : Set₁ where
  field
    S : Set
    P : S → Set

record 1ContHom (F G : 1Cont) : Set where
  open 1Cont
  field
    f : F .S → G .S
    g : (s : F .S) → G .P (f s) → F .P s

record 1⟦_⟧ (F : 1Cont) (X : Set) : Set where
  open 1Cont F
  field
    s : S
    k : P s → X

1⟦_⟧₁ : (F : 1Cont)
  → {X Y : Set} → (X → Y)
  → 1⟦ F ⟧ X → 1⟦ F ⟧ Y
1⟦ F ⟧₁ f record { s = s ; k = k }
  = record { s = s ; k = f ∘ k }

1⟦_⟧Hom : {SP TQ : 1Cont} (fg : 1ContHom SP TQ)
  → (X : Set) → 1⟦ SP ⟧ X → 1⟦ TQ ⟧ X
1⟦ record { f = f ; g = g } ⟧Hom X record { s = s ; k = k }
  = record { s = f s ; k = k ∘ g s }

record 2Cont : Set₁ where
  inductive
  eta-equality  
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

record 2ContHom (H J : 2Cont) : Set where
  inductive
  eta-equality
  open 2Cont
  field
    f : H .S → J .S
    gx : (s : H .S) → J .PX (f s) → H .PX s
    gf : (s : H .S) → J .PF (f s) → H .PF s
    hf : (s : H .S) (qf : J .PF (f s)) → 2ContHom (H .RF s (gf s qf)) (J .RF (f s) qf) 

record 2⟦_⟧ (H : 2Cont) (F : 1Cont) (X : Set) : Set where
  inductive
  eta-equality
  open 2Cont
  field
    s : H .S
    kx : H .PX s → X
    kf : (p : H .PF s) → 1⟦ F ⟧ (2⟦ H .RF s p ⟧ F X)

{-# TERMINATING #-}
2⟦_⟧₁ : (H : 2Cont)
  → {F G : 1Cont} → 1ContHom F G
  → {X Y : Set} → (X → Y)
  → 2⟦ H ⟧ F X → 2⟦ H ⟧ G Y
2⟦ H ⟧₁ {F} {G} α {X} {Y} f record { s = s ; kf = kf ; kx = kx } =
  record
  { s = s
  ; kx = f ∘ kx
  ; kf = λ pf → 1⟦ α ⟧Hom (2⟦ H. RF s pf ⟧ G Y) (1⟦ F ⟧₁ (2⟦ H .RF s pf ⟧₁ α f) (kf pf))  
  }
  where open 2Cont

{-# TERMINATING #-}
2⟦_⟧Hom : {H J : 2Cont} → 2ContHom H J
  → (F : 1Cont) (X : Set)
  → 2⟦ H ⟧ F X → 2⟦ J ⟧ F X
2⟦ record { f = f ; gf = gf ; hf = hf ; gx = gx } ⟧Hom F X
  record { s = s ; kf = kf ; kx = kx } = record
  { s = f s
  ; kx = kx ∘ gx s
  ; kf = λ pf → 1⟦ F ⟧₁ (2⟦ hf s pf ⟧Hom F X) (kf (gf s pf))  
  }

app : 2Cont → 1Cont → 1Cont
app H F = {!!}

app₁ : (H : 2Cont) → {F G : 1Cont} → 1ContHom F G → 1ContHom (app H F) (app H G)
app₁ H f = {!6!}


{-
  2⟦ S₂ , PX , PF , RF ⟧ (S , P) X
= Σ[ s₂ : S₂ ] ((PX s₂ → X) × ((pf : PF s₂) → 1⟦ S , P ⟧ (2⟦ RF s₂ p₂ ⟧ (S , P) X)))
= Σ[ s₂ : S₂ ] ((PX s₂ → X) × ((pf : PF s₂) → Σ[ s : S ] (P s → 2⟦ RF s₂ pf ⟧ (S , P) X)))

≃ Σ[ s₂ : S₂ ] ((PX s₂ → X) × (PF s₂ → Σ[ s : S ] (P s → Σ[ t : T ] (Q t → X))))

≃ Σ[ s₂ : S₂ ] ((PX s₂ → X) × (PF s₂ → Σ[ s : S ] Σ[ f : P s → T ] ((ps : P s) → Q t → X)))

≃ Σ[ s₂ : S₂ ] ((PX s₂ → X) × (PF s₂ → Σ[ (s , f) : Σ[ s : S ] (P s → T) ] ((ps : P s) → Q t → X)))

≃ Σ[ s₂ : S₂ ] ((PX s₂ → X) × Σ[ f : PF s₂ → Σ[ s : S ] (P s → T) ] ((pf : PF s₂) (ps : P (f pf .proj₁)) → Q (f pf .proj₂ ps) → X))

≃ Σ[ s₂ : S₂ ] ((PX s₂ → X) × Σ[ f : PF s₂ → Σ[ s : S ] (P s → T) ] Σ[ pf : PF s₂ ] Σ[ ps : P (f pf .proj₁) ] Q (f pf .proj₂ ps) → X)

≃ Σ[ s₂ : S₂ ] (PX s₂ × Σ[ f : PF s₂ → Σ[ s : S ] (P s → T) ] Σ[ pf : PF s₂ ] Σ[ ps : P (f pf .proj₁) ] Q (f pf .proj₂ ps) → X)

= Σ[ s' : S' ] (P' s' → X)
-}

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product

H : (Set → Set) → Set → Set
H F X = X × F (F X)

X×FFX : 2Cont
X×FFX = record { S = ⊤ ; PX = λ x → ⊤ ; PF = λ x → ⊤ ; RF = λ s x → FX }
  where
  X : 2Cont
  X = record { S = ⊤ ; PX = λ x → ⊤ ; PF = λ x → ⊥ ; RF = λ s () }
  
  FX : 2Cont
  FX = record { S = ⊤ ; PX = λ x → ⊥ ; PF = λ x → ⊤ ; RF = λ s x → X }


M : Set → Set
M X = ⊤ ⊎ X

⊤⊎X : 1Cont
⊤⊎X = record { S = Bool ; P = λ{ false → ⊥ ; true → ⊤ } }

HM : Set → Set
HM X = H M X
-- = X × M (M X)
-- = X × (⊤ ⊎ (⊤ ⊎ X))
-- = X ⊎ X ⊎ X × X

open import Data.Fin

X⊎X⊎X×X : 1Cont
X⊎X⊎X×X = record { S = Fin 3 ; P = λ{ zero → ⊤ ; (suc zero) → ⊤ ; (suc (suc zero)) → Fin 2 } }
