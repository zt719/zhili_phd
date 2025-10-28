{-# OPTIONS --cubical --guardedness #-}

module Cont.Everything where

open import Cubical.Foundations.Prelude
open import Function.Base

open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂)

variable X Y : Set

record Func : Set₁ where
  constructor _,_
  field
    F : Set → Set
    F₁ : (X → Y) → F X → F Y

NatTrans : Func → Func → Set₁
NatTrans (F , _) (G , _) = (X : Set) → F X → G X

{- ℕ Example -}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

module ℕ-Alg (α : ⊤ ⊎ X → X) where

  [z,s] : ⊤ ⊎ ℕ → ℕ
  [z,s] (inj₁ tt) = zero
  [z,s] (inj₂ n) = suc n

  foldℕ : ℕ → X
  foldℕ zero = α (inj₁ tt)
  foldℕ (suc n) = α (inj₂ (foldℕ n))

  ⊤⊎₁ : {X Y : Set} → (X → Y) → ⊤ ⊎ X → ⊤ ⊎ Y
  ⊤⊎₁ f (inj₁ tt) = inj₁ tt
  ⊤⊎₁ f (inj₂ x) = inj₂ (f x)

  commuteℕ : foldℕ ∘ [z,s] ≡ α ∘ ⊤⊎₁ foldℕ
  commuteℕ i (inj₁ tt) = α (inj₁ tt)
  commuteℕ i (inj₂ n) = α (inj₂ (foldℕ n))

{- Containers & W -}

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

variable SP TQ UV SP' TQ' : Cont

record ⟦_⟧ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    f : P s → X

⟦_⟧₁ : (SP : Cont) → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g (s , f) = s , g ∘ f

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

{- W-types as initial algebras -}

module W-as-initial-algebra (α : ⟦ SP ⟧ X → X) where

  foldW : W SP → X
  foldW (sup (s , f)) = α (s , foldW ∘ f)

  commuteW : foldW ∘ sup ≡ α ∘ ⟦ SP ⟧₁ foldW
  commuteW i (s , f) = α (s , foldW ∘ f)

module ℕ≃W-Maybe where

  data Maybe (X : Set) : Set where
    nothing : Maybe X
    just : X → Maybe X

  S : Set
  S = ⊤ ⊎ ⊤

  P : S → Set
  P (inj₁ tt) = ⊥
  P (inj₂ tt) = ⊤

  to : ℕ → W (S ◃ P)
  to zero = sup (inj₁ tt , λ ())
  to (suc n) = sup (inj₂ tt , λ{ tt → to n })

  from : W (S ◃ P) → ℕ
  from (sup (inj₁ tt , _)) = zero
  from (sup (inj₂ tt , f)) = suc (from (f tt))

  from∘to : from ∘ to ≡ id
  from∘to i zero = zero
  from∘to i (suc n) = suc (from∘to i n)

  to∘from : to ∘ from ≡ id
  to∘from i (sup (inj₁ tt , f)) = sup (inj₁ tt , h i)
    where
    h : (λ ()) ≡ f
    h i ()
  to∘from i (sup (inj₂ tt , f)) = sup (inj₂ tt , λ{ tt → to∘from i (f tt) })

{- Category of Contaiers -}

module category-of-containers where

  record _→ᶜ_ (SP TQ : Cont) : Set where
    constructor _◃_
    open Cont SP
    open Cont TQ renaming (S to T; P to Q)
    field
      g : S → T
      h : (s : S) → Q (g s) → P s

  open Cont

  ⊤ᶜ : Cont
  ⊤ᶜ = ⊤ ◃ λ _ → ⊥

  ⊥ᶜ : Cont
  ⊥ᶜ = ⊥ ◃ λ ()

  _×ᶜ_ : Cont → Cont → Cont
  (S ◃ P) ×ᶜ (T ◃ Q) = S × T ◃ λ (s , t) → P s ⊎ Q t

  _×ᶜ₁_ : SP →ᶜ TQ → SP' →ᶜ TQ' → (SP ×ᶜ SP') →ᶜ (TQ ×ᶜ TQ')
  (g ◃ h) ×ᶜ₁ (g' ◃ h')
    = (λ (s , s') → g s , g' s')
    ◃ λ{ (s , s') (inj₁ p) → inj₁ (h s p) ; (s , s') (inj₂ p') → inj₂ (h' s' p') }

  _⊎ᶜ_ : Cont → Cont → Cont
  (S ◃ P) ⊎ᶜ (T ◃ Q) = S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t }

  _⊎ᶜ₁_ : SP →ᶜ TQ → SP' →ᶜ TQ' → (SP ⊎ᶜ SP') →ᶜ (TQ ⊎ᶜ TQ')
  (g ◃ h) ⊎ᶜ₁ (g' ◃ h')
    = (λ{ (inj₁ s) → inj₁ (g s) ; (inj₂ s') → inj₂ (g' s') })
    ◃ λ{ (inj₁ s) p → h s p ; (inj₂ s') p' → h' s' p' }

  Πᶜ : (I : Set) → (I → Cont) → Cont
  Πᶜ I Cs = ((i : I) → Cs i .S) ◃ λ f → Σ[ i ∈ I ] Cs i .P (f i)
    
  infix 2 Πᶜ-syntax

  Πᶜ-syntax : (I : Set) → (I → Cont) → Cont
  Πᶜ-syntax = Πᶜ

  syntax Πᶜ-syntax A (λ x → B) = Πᶜ[ x ∈ A ] B

  Σᶜ : (I : Set) → (I → Cont) → Cont
  Σᶜ I SPs = Σ[ i ∈ I ] SPs i .S ◃ λ (i , s) → SPs i .P s

--  Σᶜ₁ : (I : Set) {SPs TQs : I → Cont} → Σ[ i ∈ I ] (SPs i →ᶜ TQs i) → Σᶜ I SPs →ᶜ Σᶜ I TQs
--  Σᶜ₁ I {SPs} {TQs} (i , (gs ◃ hs)) = (λ x → {!!}) ◃ {!!}

  infix 2 Σᶜ-syntax

  Σᶜ-syntax : (I : Set) → (I → Cont) → Cont
  Σᶜ-syntax = Σᶜ

  syntax Σᶜ-syntax A (λ x → B) = Σᶜ[ x ∈ A ] B

  _∘ᶜ_ : Cont → Cont → Cont
  (S ◃ P) ∘ᶜ (T ◃ Q) = (Σ[ s ∈ S ] (P s → T)) ◃ λ (s , f) → Σ[ p ∈ P s ] Q (f p)

  _∘ᶜ₁_ : {SP TQ UV : Cont} → TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
  (g ◃ h) ∘ᶜ₁ (g' ◃ h') = g ∘ g' ◃ λ s → h' s ∘ h (g' s)

open category-of-containers

{- Inductive types with higher kinds -}

{- List Example -}

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

List₁ : (X → Y) → List X → List Y
List₁ f [] = []
List₁ f (x ∷ xs) = f x ∷ List₁ f xs

{- List as a Container -}

module List-as-a-container where

  {- ⟦ S ◃ P ⟧ X
  -- ≃ ⊤ ⊎ X × ⟦ S ◃ P ⟧ X
  --
  -- S ◃ P
  -- ≃ (⊤ ◃ λ _ → ⊥) ⊎ᶜ ((⊤ ◃ λ _ → ⊤) ×ᶜ (S ◃ P))
  -- ≃ (⊤ ◃ λ _ → ⊥) ⊎ᶜ (S ◃ (P s ⊎ ⊤))
  -- ≃ ⊤ ⊎ S ◃ λ{ (inl tt) → ⊥ ; (inr s) → P s ⊎ ⊤ }
  -- ≃ ℕ ◃ Fin
  -}

  Fin : ℕ → Set
  Fin zero = ⊥
  Fin (suc n) = Fin n ⊎ ⊤

  fzero : {n : ℕ} → Fin (suc n)
  fzero = inj₂ tt

  fsuc : {n : ℕ} → Fin n → Fin (suc n)
  fsuc x = inj₁ x

  to : List X → ⟦ ℕ ◃ Fin ⟧ X
  to [] = zero , λ ()
  to {X} (x ∷ xs) = suc (to xs .s) , λ{ (inj₁ n) → to xs .f n ; (inj₂ tt) → x }
    where open ⟦_⟧

  {-# TERMINATING #-}
  from : ⟦ ℕ ◃ Fin ⟧ X → List X
  from (zero , _) = []
  from (suc n , f) = f fzero ∷ from (n , f ∘ fsuc)

module ListA≃W-SP (A : Set) where

  S : Set
  S = ⊤ ⊎ A

  P : S → Set
  P (inj₁ tt) = ⊥
  P (inj₂ a) = ⊤

  to : List A → W (S ◃ P)
  to [] = sup (inj₁ tt , λ ())
  to (a ∷ as) = sup (inj₂ a , λ{ tt → to as })

  from : W (S ◃ P) → List A
  from (sup (inj₁ tt , f)) = []
  from (sup (inj₂ a , f)) = a ∷ from (f tt)

  from∘to : from ∘ to ≡ id
  from∘to i [] = []
  from∘to i (a ∷ as) = a ∷ from∘to i as

  to∘from : to ∘ from ≡ id
  to∘from i (sup (inj₁ tt , f)) = sup (inj₁ tt , h i)
    where
    h : (λ ()) ≡ f
    h i ()
  to∘from i (sup (inj₂ a , f)) = sup (inj₂ a , λ{ tt → to∘from i (f tt) })
  
{- Cobush -}

data CB (X : Set) : Set where
  _∷_ : X → CB (CB X) → CB X

{-# TERMINATING #-}
CB₁ : (X → Y) → CB X → CB Y
CB₁ f (x ∷ xs) = f x ∷ CB₁ (CB₁ f) xs

module Cobush-as-a-container where

  {- ⟦ S ◃ P ⟧ X
  -- ≃ X × ⟦ S ◃ P ⟧ ⟦ S ◃ P ⟧ X
  -- 
  -- S ◃ P
  -- ≃ (⊤ ◃ λ _ → ⊤) ×ᶜ ((S ◃ P) ∘ᶜ (S ◃ P))
  -- ≃ (⊤ ◃ λ _ → ⊤) ×ᶜ (Σ[ s ∈ S ] (P s → S) ◃ λ (s , f) → Σ[ p ∈ P s ] P (f p))
  -- ≃ Σ[ s ∈ S ] (P s → S) ◃ λ (s , f) → Σ[ p ∈ P s ] (⊤ ⊎ P (f p))
  -}

  record S : Set
  
  record P (sf : S) : Set

  record S where
    inductive
    pattern
    constructor _,_
    field
      s : S
      f : P s → S

  record P sf where
    inductive
    pattern
    constructor _,_
    open S sf
    field
      p : P s
      h : ⊤ ⊎ P (f p)

{-
--  {-# TERMINATING #-}
  to : CB X → ⟦ S ◃ P ⟧ X
  to {X} (x ∷ xxs) = ({!!} , {!!}) , {!!}
    where
    open ⟦_⟧
    
    hh : ⟦ ⊤ ◃ (λ _ → ⊤) ⟧ X × ⟦ Σ[ s ∈ S ] (P s → S) ◃ (λ (s , f) → Σ[ p ∈ P s ] P (f p)) ⟧ X
    hh = (tt , (λ _ → x)) , let (s , f) = to (CB₁ to xxs) in
      (s , λ p → let (s' , f') = f p in s') , λ (p , h) → let (s' , f') = f p in f' h

    pp : ⟦ ⊤ ◃ (λ _ → ⊤) ⟧ X × ⟦ Σ[ s ∈ S ] (P s → S) ◃ (λ (s , f) → Σ[ p ∈ P s ] P (f p)) ⟧ X
      → ⟦ (Σ[ s ∈ S ] (P s → S)) ◃ (λ (s , f) → Σ[ p ∈ P s ] (⊤ ⊎ P (f p))) ⟧ X
    pp ((tt , ⊤→x) , (s , p→ll)) = s , λ{ (p , inj₁ tt) → ⊤→x tt ; (p , inj₂ h) → p→ll (p , h) }

  from : ⟦ CBCont ⟧ X → CB X
  from {X} (s , f) = ?
-}

{- Cobush as an initial algebra -}

ℂ𝔹 : Func
ℂ𝔹 = CB , CB₁

H : (Set → Set) → Set → Set
H F X = X × F (F X)

{- [ [ Set , Set ] , [ Set , Set ] ] -}

module ℍ-as-a-functor-of-functors where

  ℍ : Func → Func
  ℍ (F , F₁) = H F , HF₁
    where
    HF₁ : (X → Y) → H F X → H F Y
    HF₁ f (x , ffx) = f x , F₁ (F₁ f) ffx

  ℍ₁ : {𝔽 𝔾 : Func} → NatTrans 𝔽 𝔾 → NatTrans (ℍ 𝔽) (ℍ 𝔾)
  ℍ₁ {F , F₁} {G , G₁} α X (x , ffx) = x , α (G X) (F₁ (α X) ffx)

  module _ (𝔽 : Func) (α : NatTrans (ℍ 𝔽) 𝔽) where

    open Func 𝔽

    inCB : NatTrans (ℍ ℂ𝔹) ℂ𝔹
    inCB X (x , xxs) = x ∷ xxs

    {-# TERMINATING #-}
    foldCB : NatTrans ℂ𝔹 𝔽
    foldCB X (x ∷ xxs) = α X (x , foldCB (F X) (CB₁ (foldCB X) xxs))

    _∘nt_ : {F₁ F₂ F₃ : Func} → NatTrans F₂ F₃ → NatTrans F₁ F₂ → NatTrans F₁ F₃
    (α ∘nt β) X x = α X (β X x)

    commuteCB : _∘nt_ {ℍ ℂ𝔹} {ℂ𝔹} {𝔽} foldCB inCB
      ≡ _∘nt_ {ℍ ℂ𝔹} {ℍ 𝔽} {𝔽} α (ℍ₁ {ℂ𝔹} {𝔽} foldCB)
    commuteCB i X (x , xxs) = α X (x , foldCB (F X) (CB₁ (foldCB X) xxs))

module ℍ-as-a-functor-of-containers where

  ℍ : Cont → Cont
  ℍ (S ◃ P) = (S' ◃ P')
    where
    S' : Set
    S' = Σ[ s ∈ S ] (P s → S)
    
    P' : S' → Set
    P' (s , f) = Σ[ p ∈ P s ] (⊤ ⊎ P (f p))
  
  ℍ₁ : SP →ᶜ TQ → ℍ SP →ᶜ ℍ TQ
  ℍ₁ {S ◃ P} {T ◃ Q} (g ◃ h) = g' ◃ h'
    where
    g' : Σ[ s ∈ S ] (P s → S) → Σ[ t ∈ T ] (Q t → T)
    g' (s , f) = g s , g ∘ f ∘ h s

    h' : ((s , f) : Σ[ s ∈ S ] (P s → S))
      → Σ[ q ∈ Q (g s) ] (⊤ ⊎ Q (g (f (h s q))))
      → Σ[ p ∈ P s ] (⊤ ⊎ P (f p))
    h' (s , f) (q , inj₁ tt) = h s q , inj₁ tt
    h' (s , f) (q , inj₂ k) = h s q , inj₂ (h (f (h s q)) k)

  module _ (TQ : Cont) (ab : ℍ TQ →ᶜ TQ) where

    open Cobush-as-a-container

    inCB : ℍ (S ◃ P) →ᶜ (S ◃ P)
    inCB = g ◃ h
      where
      g : Σ[ s ∈ S ] (P s → S) → S
      g (s , f) = s , f

      h : ((s , f) : Σ[ s ∈ S ] (P s → S))
        → P (s , f) → Σ[ p ∈ P s ] ⊤ ⊎ P (f p)
      h (s , f) (p , inj₁ tt) = p , inj₁ tt
      h (s , f) (p , inj₂ k) = p , inj₂ k

    open Cont TQ renaming (S to T; P to Q)
    open _→ᶜ_ ab renaming (g to a; h to b)

{-
--   {-# TERMINATING #-}
    foldCB : (S ◃ P) →ᶜ (T ◃ Q)
    foldCB = {!!}
      where
      g : S → T
      g (s , f) = {!!}
      
      h : (s : S) → Q (g s) → P s
      h (s , f) = {!!}
-}
  --  commuteCB : foldCB ∘ᶜ₁ inCB ≡ gh ∘ᶜ₁ ℍ₁ foldCB
  --  commuteCB = {!!}

{- H-as-a-container-of-containers -}

{- Second-order Containers -}

record 2Cont : Set₁ where
  constructor _◃_+_+_
  pattern
  inductive
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

record 2⟦_⟧ (H : 2Cont) (F : Cont) (X : Set) : Set where
  constructor _,_,_
  inductive
  pattern
  open 2Cont H
  field
    s : S
    kx : PX s → X
    kf : (pf : PF s) → ⟦ F ⟧ (2⟦ RF s pf ⟧ F X)

{-
ℍ-2Cont : 2Cont
ℍ-2Cont = ⊤ ◃ (λ{ tt → ⊤ }) + (λ{ tt → ⊤ }) + (λ{ tt tt → FX-2Cont })
  where
  FX-2Cont : 2Cont
  FX-2Cont = ⊤ ◃ (λ{ tt → ⊥ }) + (λ{ tt → ⊤ }) + λ{ tt tt → X-2Cont }
    where
    X-2Cont : 2Cont
    X-2Cont = ⊤ ◃ (λ{ tt → ⊤ }) + (λ{ tt → ⊥ }) + λ{ tt () }
-}

{- Application ? -}

appS : 2Cont → Cont → Set
appS (S ◃ PX + PF + RF) (T ◃ Q) = Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pf) (T ◃ Q)))

appP : (H : 2Cont) (F : Cont) → appS H F → Set
appP (S ◃ PX + PF + RF) (T ◃ Q) (s , f) = Σ[ pf ∈ PF s ] let (t , g) = f pf in Σ[ q ∈ Q t ] (appP (RF s pf) (T ◃ Q) (g q) ⊎ PX s) 

app : 2Cont → Cont → Cont
app H F = appS H F ◃ appP H F

{-
app : 2Cont → Cont → Cont
app (S ◃ PX + PF + RF) TQ
  = Σᶜ[ s ∈ S ] ((⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ[ pf ∈ PF s ] (TQ ∘ᶜ app (RF s pf) TQ)))
-}

{-
  let (S' ◃ P') = app (RF s pf) TQ

= Σᶜ s : S, ((⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, ((T ◃ Q) ∘ᶜ (S' ◃ P'))))
= Σᶜ s : S, ((⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, (Σ t : T, (Q t → S') ◃ λ (t , f) → Σ q : Q t, P' (f q)))
= Σᶜ s : S, ((⊤ ◃ λ _ → PX s) ×ᶜ (Π pf : PF s, (Σ t : T, (Q t → S') ◃ λ (t , f) → Σ q : Q t, P' (f q)))

  IH : (s : S) (pf : PF s) → 2⟦ RF s pf ⟧ TQ X ≃ ⟦ app (RF s pf) TQ ⟧ X

  2⟦ S ◃ PX + PF + RF ⟧ TQ X
= Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⟧ (2⟦ RF s pf ⟧ TQ X))
= Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⟧ (⟦ app (RF s pf) TQ ⟧ X))
= Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ∘ᶜ app (RF s pf) TQ ⟧ X)
= Σ s : S, (PX s → X) × (⟦ Πᶜ pf : PF s, TQ ∘ᶜ app (RF s pf) TQ ⟧ X)
= Σ s : S, (⟦ ⊤ ◃ λ _ → PX s ⟧ X) × (⟦ Πᶜ pf : PF s, TQ ∘ᶜ app (RF s pf) TQ ⟧ X)
= Σ s : S, ⟦ (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ∘ᶜ app (RF s pf) TQ) ⟧ X
= ⟦ Σᶜ s : S, (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ∘ᶜ (app (RF s pf) TQ)) ⟧ X
= ⟦ Σᶜ s : S, (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ∘ᶜ (app (RF s pf) TQ)) ⟧ X
= ⟦ app (S ◃ PX + PF + RF) TQ ⟧ X
-}

{-
app₁ : (H : 2Cont) → SP →ᶜ TQ → app H SP →ᶜ app H TQ
app₁ {SP} {TQ} H gh = {!!}
-}

{-
inCB : app ℍ-2Cont CB-Cont →ᶜ CB-Cont
inCB = {!!} ◃ {!!}
  wherepp
  open Cont CB-Cont renaming (S to T; P to Q)
  open 2Cont ℍ-2Cont
-}

{- Second-order W -}

{-
data 2WS (H : 2Cont) : Set

2WP : (H : 2Cont) → 2WS H → Set

data 2WS H where
  supS : appS H (2WS H ◃ 2WP H) → 2WS H

2WP (S ◃ PX + PF + RF) (supS (s , f))
  = Σ[ pf ∈ PF s ] let (t , g) = f pf in Σ[ q ∈ 2WP (S ◃ PX + PF + RF) t ]
  appP (RF s pf) (2WS (S ◃ PX + PF + RF) ◃ 2WP (S ◃ PX + PF + RF)) (g q)

2W : 2Cont → Cont
2W H = 2WS H ◃ 2WP H

--2sup : {H : 2Cont} → app H (2W H) →ᶜ 2W H
--2sup = {!!}
-}

liftᶜ : Cont → 2Cont
liftᶜ (S ◃ P) = S ◃ P + (λ _ → ⊥) + λ s ()

data Maybe' (F : Set → Set) (X : Set) : Set where
  nothing : Maybe' F X
  just : X → Maybe' F X
