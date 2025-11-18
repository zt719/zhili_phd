{-# OPTIONS  --guardedness #-}

module Cont.Every where

open import Function.Base

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality

postulate
  funExt : {A : Set} {B : A → Set}
    {f g : (x : A) → B x}
    (p : (x : A) → f x ≡ g x)
    → f ≡ g

funExt⁻ : {A : Set} {B : A → Set}
  {f g : (x : A) → B x}
  (p : f ≡ g)
  (x : A) → f x ≡ g x
funExt⁻ refl x = refl

case : {A B : Set} → (A → Set) → (B → Set) → A ⊎ B → Set
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

infixr 4 _,_

variable X Y : Set

record Func : Set₁ where
  constructor _,_
  field
    F : Set → Set
    F₁ : (X → Y) → F X → F Y

NatTrans : Func → Func → Set₁
NatTrans (F , _) (G , _) = (X : Set) → F X → G X

{- Natural Number -}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

module _ (X : Set) (α : ⊤ ⊎ X → X) where

--  ⊤ ⊎ ℕ → ⊤ ⊎ X
--    ↓       ↓
--    ℕ   →   X

  [z,s] : ⊤ ⊎ ℕ → ℕ
  [z,s] (inj₁ tt) = zero
  [z,s] (inj₂ n) = suc n

  foldℕ : ℕ → X
  foldℕ zero = α (inj₁ tt)
  foldℕ (suc n) = α (inj₂ (foldℕ n))

  ⊤⊎₁ : {X Y : Set} → (X → Y) → ⊤ ⊎ X → ⊤ ⊎ Y
  ⊤⊎₁ f (inj₁ tt) = inj₁ tt
  ⊤⊎₁ f (inj₂ x) = inj₂ (f x)

  commuteℕ : (a : ⊤ ⊎ ℕ) → foldℕ ([z,s] a) ≡ α (⊤⊎₁ foldℕ a)
  commuteℕ (inj₁ tt) = refl
  commuteℕ (inj₂ n) = refl

  !foldℕ : (foldℕ' : ℕ → X)
    (commuteℕ' : (a : ⊤ ⊎ ℕ) → foldℕ' ([z,s] a) ≡ α (⊤⊎₁ foldℕ' a))
    (n : ℕ) → foldℕ' n ≡ foldℕ n
  !foldℕ foldℕ' commuteℕ' zero = commuteℕ' (inj₁ tt)
  !foldℕ foldℕ' commuteℕ' (suc n)
    = trans (commuteℕ' (inj₂ n)) (cong (α ∘ inj₂) (!foldℕ foldℕ' commuteℕ' n))
  
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

record Eq⟦⟧ (sf sf' : ⟦ SP ⟧ X) : Set₁ where
  constructor _,_
  open Cont SP
  open ⟦_⟧ sf
  open ⟦_⟧ sf' renaming (s to s'; f to f')
  field
    eqs : s ≡ s'
    eqf : (p : P s) → f p ≡ f' (subst P eqs p)

Eq⟦⟧-to-≡ : {S : Set} {P : S → Set}
  {s s' : S} {f : P s → X} {f' : P s' → X}
  → Eq⟦⟧ (s , f) (s' , f')
  → _≡_ {A = ⟦ S ◃ P ⟧ X} (s , f) (s' , f')
Eq⟦⟧-to-≡ (refl , eqf) with funExt eqf
... | refl = refl

{-
⟦⟧≡ : {S : Set} {P : S → Set}
  {s s' : S} {f : P s → X} {f' : P s' → X}
  → Σ[ eqs ∈ s ≡ s' ] ((p : P s) → f p ≡ f' (subst P eqs p))
  → _≡_ {A = ⟦ S ◃ P ⟧ X} (s , f) (s' , f')
⟦⟧≡ (refl , eqf) with funExt eqf
... | refl = {!!}
-}

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

module _ (X : Set) (α : ⟦ SP ⟧ X → X) where

-- ⟦ SP ⟧ (W SP) → ⟦ SP ⟧ X
--      ↓              ↓
--     W SP      →     X

  foldW : W SP → X
  foldW (sup (s , f)) = α (s , foldW ∘ f)

  commuteW : (sf : ⟦ SP ⟧ (W SP)) → foldW (sup sf) ≡ α (⟦ SP ⟧₁ foldW sf)
  commuteW sf = refl

  !foldW : (foldW' : W SP → X)
    (commuteW' : (sf : ⟦ SP ⟧ (W SP)) → foldW' (sup sf) ≡ α (⟦ SP ⟧₁ foldW' sf)) → 
    (w : W SP) → foldW' w ≡ foldW w
  !foldW foldW' commuteW' (sup (s , f))
    = trans (commuteW' (s , f)) (cong α (Eq⟦⟧-to-≡ (refl , λ p → !foldW foldW' commuteW' (f p))))

module ℕ≃W-Maybe where

  data Maybe (X : Set) : Set where
    nothing : Maybe X
    just : X → Maybe X

  S : Set
  S = ⊤ ⊎ ⊤

  P : S → Set
  P (inj₁ tt) = ⊥
  P (inj₂ tt) = ⊤

  Maybeᶜ : Cont
  Maybeᶜ = S ◃ P

  to : ℕ → W Maybeᶜ
  to zero = sup (inj₁ tt , λ ())
  to (suc n) = sup (inj₂ tt , λ{ tt → to n })

  from : W Maybeᶜ → ℕ
  from (sup (inj₁ tt , _)) = zero
  from (sup (inj₂ tt , f)) = suc (from (f tt))

  from∘to : (n : ℕ) → from (to n) ≡ n
  from∘to zero = refl
  from∘to (suc n) = cong suc (from∘to n)

  to∘from : (w : W Maybeᶜ) → to (from w) ≡ w
  to∘from (sup (inj₁ tt , f)) = cong sup (Eq⟦⟧-to-≡ (refl , λ ()))
  to∘from (sup (inj₂ tt , f)) = cong sup (Eq⟦⟧-to-≡ (refl , λ{ tt → to∘from (f tt) }))

{- Category of Contaiers -}

record _→ᶜ_ (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    g : S → T
    h : (s : S) → Q (g s) → P s

⟦_⟧→ᶜ : SP →ᶜ TQ → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ g ◃ h ⟧→ᶜ X (s , f) = g s , f ∘ h s

idᶜ : SP →ᶜ SP
idᶜ = id ◃ λ s → id

∘ᶜ : TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
∘ᶜ (g ◃ h) (g' ◃ h') = (g ∘ g') ◃ λ s → h' s ∘ h (g' s)

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
Πᶜ I Cs = ((i : I) → let S ◃ _ = Cs i in S) ◃ λ f → Σ[ i ∈ I ] let _ ◃ P = Cs i in P (f i)

infix 2 Πᶜ-syntax

Πᶜ-syntax : (I : Set) → (I → Cont) → Cont
Πᶜ-syntax = Πᶜ

syntax Πᶜ-syntax A (λ x → B) = Πᶜ[ x ∈ A ] B

Πᶜ₁ : (I : Set) {SPs TQs : I → Cont} → ((i : I) → SPs i →ᶜ TQs i) → Πᶜ I SPs →ᶜ Πᶜ I TQs
Πᶜ₁ I f = (λ s i → let g ◃ _ = f i in g (s i))
  ◃ λ s (i , p) → i , let _ ◃ h = f i in h (s i) p

Σᶜ : (I : Set) → (I → Cont) → Cont
Σᶜ I SPs = (Σ[ i ∈ I ] let S ◃ _ = SPs i in S) ◃ λ (i , s) → let _ ◃ P = SPs i in P s

infix 2 Σᶜ-syntax

Σᶜ-syntax : (I : Set) → (I → Cont) → Cont
Σᶜ-syntax = Σᶜ

syntax Σᶜ-syntax A (λ x → B) = Σᶜ[ x ∈ A ] B

Σᶜ₁ : (I : Set) {SPs TQs : I → Cont} → ((i : I) → SPs i →ᶜ TQs i) → Σᶜ I SPs →ᶜ Σᶜ I TQs
Σᶜ₁ I f = (λ{ (i , s) → i , let g ◃ _ = f i in g s})
  ◃ λ{ (i , s) p → let _ ◃ h = f i in h s p }

_⊗ᶜ_ : Cont → Cont → Cont
(S ◃ P) ⊗ᶜ (T ◃ Q) = (Σ[ s ∈ S ] (P s → T)) ◃ λ (s , f) → Σ[ p ∈ P s ] Q (f p)

_⊗ᶜ₁_ : {SP TQ SP' TQ' : Cont} → SP →ᶜ TQ → SP' →ᶜ TQ' → (SP ⊗ᶜ SP') →ᶜ (TQ ⊗ᶜ TQ')
(g ◃ h) ⊗ᶜ₁ (g' ◃ h') = (λ (s , f) → g s , g' ∘ f ∘ h s)
  ◃ λ{ (s , f) (q , q') → h s q , h' (f (h s q)) q' }

{- List -}

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

List₁ : (X → Y) → List X → List Y
List₁ f [] = []
List₁ f (x ∷ xs) = f x ∷ List₁ f xs

{- List as a Container -}

module List-Cont where

  {- ⟦ S ◃ P ⟧ X
  -- ≃ ⊤ ⊎ X × ⟦ S ◃ P ⟧ X
  -- ≃ ⟦ ⊤ᶜ ⟧ X ⊎ ⟦ ⊤ ◃ λ _ → ⊤ ⟧ X × ⟦ S ◃ P ⟧ X
  --
  -- S ◃ P
  -- ≃ (⊤ ◃ λ _ → ⊥) ⊎ᶜ ((⊤ ◃ λ _ → ⊤) ×ᶜ (S ◃ P))
  -- ≃ (⊤ ◃ λ _ → ⊥) ⊎ᶜ (S ◃ (λ s → ⊤ ⊎ P s))
  -- ≃ ⊤ ⊎ S ◃ λ{ (inl tt) → ⊥ ; (inr s) → ⊤ ⊎ P s }
  -- ≃ ℕ ◃ Fin
  -}
  
  Fin : ℕ → Set
  Fin zero = ⊥
  Fin (suc n) = ⊤ ⊎ Fin n

  Listᶜ : Cont
  Listᶜ = ℕ ◃ Fin
  
  to : List X → ⟦ Listᶜ ⟧ X
  to [] = zero , λ ()
  to (x ∷ xs) = suc (to xs .s) , λ{ (inj₁ tt) → x ; (inj₂ i) → to xs .f i }
    where open ⟦_⟧

  {-# TERMINATING #-}
  from : ⟦ Listᶜ ⟧ X → List X
  from (zero , _) = []
  from (suc n , f) = f (inj₁ tt) ∷ from (n , f ∘ inj₂)

  from∘to : (xs : List X) → from (to xs) ≡ xs
  from∘to [] = refl
  from∘to (x ∷ xs) = cong₂ _∷_ refl (from∘to xs)

  {-
  {-# TERMINATING #-}
  to∘from : (sf : ⟦ Listᶜ ⟧ X) → to (from sf) ≡ sf
  to∘from (zero , f) = Eq⟦⟧-to-≡ (refl , λ ())
  to∘from (suc n , f) = Eq⟦⟧-to-≡ (cong (suc ∘ ⟦_⟧.s) hh
    , λ{ (inj₁ tt) → {!cong ⟦_⟧.f!} ; (inj₂ y) → {!!} })
    where
    hh : to (from (n , f ∘ inj₂)) ≡ (n , f ∘ inj₂)
    hh = to∘from (n , f ∘ inj₂)
  -}
  
{- List A as a W-type -}

module ListA≃W-⊤⊎A×Xᶜ (A : Set) where

  S : Set
  S = ⊤ ⊎ A

  P : S → Set
  P (inj₁ tt) = ⊥
  P (inj₂ a) = ⊤

  ⊤⊎A×Xᶜ : Cont
  ⊤⊎A×Xᶜ = S ◃ P

  to : List A → W ⊤⊎A×Xᶜ
  to [] = sup (inj₁ tt , λ ())
  to (a ∷ as) = sup (inj₂ a , λ{ tt → to as })

  from : W ⊤⊎A×Xᶜ → List A
  from (sup (inj₁ tt , f)) = []
  from (sup (inj₂ a , f)) = a ∷ from (f tt)

  from∘to : (as : List A) → from (to as) ≡ as
  from∘to [] = refl
  from∘to (a ∷ as) = cong₂ _∷_ refl (from∘to as)

  to∘from : (w : W ⊤⊎A×Xᶜ) → to (from w) ≡ w
  to∘from (sup (inj₁ tt , f)) = cong sup (Eq⟦⟧-to-≡ (refl , λ ()))
  to∘from (sup (inj₂ y , f)) = cong sup (Eq⟦⟧-to-≡ (refl , λ{ tt → to∘from (f tt) }))

{- Weird List -}

data LList (X : Set) : Set where
  [] : LList X
  _∷_ : X → LList (LList X) → LList X

{-# TERMINATING #-}
LList₁ : (X → Y) → LList X → LList Y
LList₁ f [] = []
LList₁ f (x ∷ xs) = f x ∷ LList₁ (LList₁ f) xs

𝕃List : Func
𝕃List = LList , LList₁

{- LList is a Container -}

module LList-Cont where

  {- ⟦ S ◃ P ⟧ X
  -- ≃ ⊤ ⊎ X × ⟦ S ◃ P ⟧ ⟦ S ◃ P ⟧ X
  -- ≃ (⊤ ◃ λ _ → ⊥) X ⊎ (⊤ ◃ λ _ ⊤) X × ⟦ S ◃ P ⟧ ⟦ S ◃ P ⟧ X
  -- 
  -- S ◃ P
  -- ≃ ⊤ᶜ ⊎ᶜ (⊤ ◃ λ _ → ⊤) ×ᶜ ((S ◃ P) ⊗ᶜ (S ◃ P))
  -- ≃ ⊤ᶜ ⊎ᶜ (⊤ ◃ λ _ → ⊤) ×ᶜ (Σ[ s ∈ S ] (P s → S) ◃ λ (s , f) → Σ[ p ∈ P s ] P (f p))
  -- ≃ ⊤ᶜ ⊎ᶜ Σ[ s ∈ S ] (P s → S) ◃ λ (s , f) → ⊤ ⊎ Σ[ p ∈ P s ] (⊤ ⊎ P (f p))
  -- ≃ (⊤ ⊎ Σ[ s ∈ S ] (P s → S))
     ◃ case (λ{ tt → ⊥ }) (λ{ (s , f) → ⊤ ⊎ Σ[ p ∈ P s ] P (f p) })
  -}

  record S : Set

  record P (s : S) : Set

  record S where
    constructor InS
    pattern    
    inductive
    field
      OutS : ⊤ ⊎ (Σ[ s ∈ S ] (P s → S))
  open S

  record P s where
    constructor InP
    pattern
    inductive
    field
      OutP : case (λ{ tt → ⊥ }) (λ{ (s , f) → ⊤ ⊎ (Σ[ p ∈ P s ] P (f p)) }) (OutS s)
  open P

  LListᶜ : Cont
  LListᶜ = S ◃ P

  {-
  to : LList X → ⟦ LListᶜ ⟧ X
  to [] = InS (inj₁ tt) , λ ()
  to {X} (x ∷ xxs) = InS (inj₂ ({!!} , {!!}))
    , λ{ (InP (inj₁ tt)) → x ; (InP (inj₂ (p , p'))) → {!h .f!} }
    where
    open ⟦_⟧
    
    h : ⟦ LListᶜ ⟧ (⟦ LListᶜ ⟧ X)
    h = to (LList₁ to xxs)

  from : ⟦ LListᶜ ⟧ X → LList X
  from = {!!}
  -}
  
{- H as a Functor of Functors -}

H : (Set → Set) → Set → Set
H F X = ⊤ ⊎ (X × F (F X))

module ℍ-Func-Func where

  ℍ : Func → Func
  ℍ (F , F₁) = H F , HF₁
    where
    HF₁ : (X → Y) → H F X → H F Y
    HF₁ f (inj₁ tt) = inj₁ tt
    HF₁ f (inj₂ (x , xxs)) = inj₂ (f x , F₁ (F₁ f) xxs)

  ℍ₁ : {𝔽 𝔾 : Func} → NatTrans 𝔽 𝔾 → NatTrans (ℍ 𝔽) (ℍ 𝔾)
  ℍ₁ α X (inj₁ tt) = inj₁ tt
  ℍ₁ {F , F₁} {G , G₁} α X (inj₂ (x , ffx)) = inj₂ (x , α (G X) (F₁ (α X) ffx))

  module _ (𝔽 : Func) (α : NatTrans (ℍ 𝔽) 𝔽) where

  -- ℍ 𝕃List → ℍ 𝔽
  --    ↓       ↓
  --  𝕃List  →  𝔽
  
    open Func 𝔽

    in𝕃List : NatTrans (ℍ 𝕃List) 𝕃List
    in𝕃List X (inj₁ tt) = []
    in𝕃List X (inj₂ (x , xxs)) = x ∷ xxs

    {-# TERMINATING #-}
    fold𝕃List : NatTrans 𝕃List 𝔽
    fold𝕃List X [] = α X (inj₁ tt)
    fold𝕃List X (x ∷ xxs) = α X (inj₂ (x , fold𝕃List (F X) (LList₁ (fold𝕃List X) xxs)))

    _∘nt_ : {F₁ F₂ F₃ : Func} → NatTrans F₂ F₃ → NatTrans F₁ F₂ → NatTrans F₁ F₃
    (α ∘nt β) X x = α X (β X x)

{-
  commute𝕃List : (a : ℍ 𝕃List) (X : Set) → ?
      → fold𝕃List X (in𝕃List X a) ≡ 
      ≡ α X (ℍ₁ fold𝕃List X a)
    commute𝕃List i X (inj₁ tt) = α X (inj₁ tt)  
    commute𝕃List i X (inj₂ (x , xxs)) = α X (inj₂ (x , fold𝕃List (F X) (LList₁ (fold𝕃List X) xxs)))

{- H as a Functor of Containers -}

module ℍ-Func-Cont where

  ℍ : Cont → Cont
  ℍ (S ◃ P) = (S' ◃ P')
    where
    S' : Set
    S' = ⊤ ⊎ (Σ[ s ∈ S ] (P s → S))
    
    P' : S' → Set
    P' (inj₁ tt) = ⊥
    P' (inj₂ (s , f)) = ⊤ ⊎ (Σ[ p ∈ P s ] P (f p))

  ℍ₁ : SP →ᶜ TQ → ℍ SP →ᶜ ℍ TQ
  ℍ₁ {SP} {TQ} (g ◃ h) = g' ◃ h'
    where
    open Cont (ℍ SP) renaming (S to S'; P to P')
    open Cont (ℍ TQ) renaming (S to T'; P to Q')    

    g' : S' → T'
    g' (inj₁ tt) = inj₁ tt
    g' (inj₂ (s , f)) = inj₂ (g s , g ∘ f ∘ h s)

    h' : (s' : S') → Q' (g' s') → P' s'
    h' (inj₂ (s , f)) (inj₁ tt) = inj₁ tt
    h' (inj₂ (s , f)) (inj₂ (p , p')) = inj₂ (h s p , h (f (h s p)) p')

  module _ (TQ : Cont) (ab : ℍ TQ →ᶜ TQ) where

    -- ℍ LListᶜ → ℍ TQ
    --   ↓        ↓
    --  LListᶜ  →  TQ

    open LList-Cont

    inLListᶜ : ℍ LListᶜ →ᶜ LListᶜ
    inLListᶜ = g ◃ h
      where
      open Cont (ℍ LListᶜ) renaming (S to S'; P to P')
      
      g : S' → S
      g (inj₁ tt) = InS (inj₁ tt)
      g (inj₂ (s , f)) = InS (inj₂ (s , f))

      h : (s' : S') → P (g s') → P' s'
      h (inj₂ (s , f)) (InP (inj₁ tt)) = inj₁ tt
      h (inj₂ (s , f)) (InP (inj₂ (p , p'))) = inj₂ (p , p')

    open Cont TQ renaming (S to T; P to Q)
    open _→ᶜ_ ab renaming (g to a; h to b)

    {-
    foldLListᶜ : (S ◃ P) →ᶜ (T ◃ Q)
    foldLListᶜ = g ◃ {!!}
      where
      g : S → T
      g (InS (inj₁ tt)) = a (inj₁ tt)
      g (InS (inj₂ (s , f))) = a (inj₂ (g s , {!!}))

    commuteLListᶜ : foldLListᶜ ∘ᶜ₁ inLListᶜ ≡ gh ∘ᶜ₁ ℍ₁ foldLListᶜ
    commuteLListᶜ = {!!}
    -}
    
{- H-as-a-container-of-containers -}

{- Second-Order Containers -}

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
  constructor _&_&_
  inductive
  pattern
  open 2Cont H
  field
    s : S
    kx : PX s → X
    kf : (pf : PF s) → ⟦ F ⟧ (2⟦ RF s pf ⟧ F X)

-- H F X = ⊤ ⊎ X × F (F X)

ℍ²ᶜ : 2Cont
ℍ²ᶜ = (⊤ ⊎ ⊤) ◃ (λ{ (inj₁ tt) → ⊥ ; (inj₂ tt) → ⊤ })
  + (λ{ (inj₁ tt) → ⊥ ; (inj₂ tt) → ⊤ })
  + λ{ (inj₂ tt) tt → FX²ᶜ }
  where
  FX²ᶜ : 2Cont
  FX²ᶜ = ⊤ ◃ (λ{ tt → ⊥ }) + (λ{ tt → ⊤ }) + λ{ tt tt → X²ᶜ }
    where
    X²ᶜ : 2Cont
    X²ᶜ = ⊤ ◃ (λ{ tt → ⊤ }) + (λ{ tt → ⊥ }) + λ{ tt () }

{-
app : 2Cont → Cont → Cont
app (S ◃ PX + PF + RF) TQ
  = Σᶜ[ s ∈ S ] ((⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ[ pf ∈ PF s ] (TQ ⊗ᶜ app (RF s pf) TQ)))
-}

appS : 2Cont → Cont → Set
appS (S ◃ PX + PF + RF) (T ◃ Q) = Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pf) (T ◃ Q)))

appP : (H : 2Cont) (F : Cont) → appS H F → Set
appP (S ◃ PX + PF + RF) (T ◃ Q) (s , f) = Σ[ pf ∈ PF s ] let (t , g) = f pf in Σ[ q ∈ Q t ] (appP (RF s pf) (T ◃ Q) (g q) ⊎ PX s) 

app : 2Cont → Cont → Cont
app H F = appS H F ◃ appP H F
  
{-
  IH : (s : S) (pf : PF s) → 2⟦ RF s pf ⟧ TQ X ≃ ⟦ app (RF s pf) TQ ⟧ X

  2⟦ S ◃ PX + PF + RF ⟧ TQ X
≃ Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⟧ (2⟦ RF s pf ⟧ TQ X))
≃ Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⟧ (⟦ app (RF s pf) TQ ⟧ X))
≃ Σ s : S, (PX s → X) × ((pf : PF s) → ⟦ TQ ⊗ᶜ app (RF s pf) TQ ⟧ X)
≃ Σ s : S, (PX s → X) × (⟦ Πᶜ pf : PF s, TQ ⊗ᶜ app (RF s pf) TQ ⟧ X)
≃ Σ s : S, (⟦ ⊤ ◃ λ _ → PX s ⟧ X) × (⟦ Πᶜ pf : PF s, TQ ⊗ᶜ app (RF s pf) TQ ⟧ X)
≃ Σ s : S, ⟦ (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ⊗ᶜ app (RF s pf) TQ) ⟧ X
≃ ⟦ Σᶜ s : S, (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ⊗ᶜ (app (RF s pf) TQ)) ⟧ X
≃ ⟦ Σᶜ s : S, (⊤ ◃ λ _ → PX s) ×ᶜ (Πᶜ pf : PF s, TQ ⊗ᶜ (app (RF s pf) TQ)) ⟧ X
≃ ⟦ app (S ◃ PX + PF + RF) TQ ⟧ X
-}

appS₁ : (SPPR : 2Cont) → TQ →ᶜ UV → appS SPPR TQ → appS SPPR UV
appS₁ (S ◃ PX + PF + RF) (g ◃ h) (s , f)
  = s , λ pf → let (t , f') = f pf in
    g t , λ u → appS₁ (RF s pf) (g ◃ h) (f' (h t u))

appP₁ : (SPPR : 2Cont) (gh : TQ →ᶜ UV) (s : appS SPPR TQ) → appP SPPR UV (appS₁ SPPR gh s) → appP SPPR TQ s
appP₁ (S ◃ PX + PF + RF) (g ◃ h) (s , f) (pf , u , inj₁ p')
  = let (t , f') = f pf in pf , h t u , inj₁ (appP₁ (RF s pf) (g ◃ h) (f' (h t u)) p')
appP₁ (S ◃ PX + PF + RF) (g ◃ h) (s , f) (pf , u , inj₂ px)
  = let (t , f') = f pf in pf , h t u , inj₂ px

app₁ : (H : 2Cont) → SP →ᶜ TQ → app H SP →ᶜ app H TQ
app₁ H gh = appS₁ H gh ◃ appP₁ H gh

module H-Cont-Cont where

  module _ (UV : Cont) (ab : app ℍ²ᶜ UV →ᶜ UV) where

  -- app ℍ²ᶜ LListᶜ → app ℍ²ᶜ TQ
  --       ↓               ↓
  --     LListᶜ     →     TQ

  open 2Cont ℍ²ᶜ
  open LList-Cont renaming (S to T; P to Q)

  {-
  inLList : app ℍ²ᶜ LListᶜ →ᶜ LListᶜ
  inLList = g ◃ {!!}
    where
    g : appS ℍ²ᶜ LListᶜ → T
    g = {!!}
  -}

{- Second-order W -}

{-
appS : 2Cont → Cont → Set
appS (S ◃ PX + PF + RF) (T ◃ Q) = Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ T ] (Q t → appS (RF s pf) (T ◃ Q)))
-}

{-
record 2WS (H : 2Cont) : Set

record 2WP (H : 2Cont) (s : 2WS H) : Set

record 2WS H where
  constructor 2supS
  inductive
  pattern
  open 2Cont H
  field
    2infS : Σ[ s ∈ S ] ((pf : PF s) → {!!})

record 2WP H s where
  constructor 2supP
  inductive
  pattern
  field
    2infP : {!!}
-}  

{-
2WP (S ◃ PX + PF + RF) (2supS (s , f))
  = Σ[ pf ∈ PF s ] let (t , g) = f pf in Σ[ q ∈ 2WP (S ◃ PX + PF + RF) t ]
  appP (RF s pf) (2WS (S ◃ PX + PF + RF) ◃ 2WP (S ◃ PX + PF + RF)) (g q)
-}
{-
2W : 2Cont → Cont
2W H = 2WS H ◃ 2WP H

2supP : {H : 2Cont} → (s : appS H (2WS H ◃ 2WP H)) → 2WP H (2supS s) → appP H (2WS H ◃ 2WP H) s
2supP s x = {!!}

2sup : {H : 2Cont} → app H (2W H) →ᶜ 2W H
2sup = 2supS ◃ 2supP
-}

{-
module _ (TQ : Cont) (ab : app ℍ²ᶜ TQ →ᶜ TQ) where

  -- app ℍ²ᶜ (2W ℍ²ᶜ) → app ℍ²ᶜ TQ
  --       ↓               ↓
  --     2W ℍ²ᶜ       →   TQ

  fold2W : {H : 2Cont} → 2W H →ᶜ TQ
  fold2W = {!!}
-}  

module category-of-2containers where

  record _→²ᶜ_ (SPPR TQQL : 2Cont) : Set₁ where
    inductive
    constructor _+_+_+_
    pattern
    open 2Cont SPPR
    open 2Cont TQQL renaming (S to T; PX to QX; PF to QF; RF to LF)
    field
      g : S → T
      hx : (s : S) → QX (g s) → PX s
      hf : (s : S) → QF (g s) → PF s
      kf : (s : S) (q : QF (g s)) → RF s (hf s q) →²ᶜ LF (g s) q

  ⟦_⟧→²ᶜ : {H J : 2Cont} → H →²ᶜ J → (UV : Cont) → app H UV →ᶜ app J UV
  ⟦ α ⟧→²ᶜ UV = g' α UV ◃ h' α UV
    where
    g' : {H J : 2Cont} → H →²ᶜ J → (UV : Cont) → appS H UV → appS J UV
    g' {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (g + hx + hf + kf) UV (s , f)
      = g s , λ qf → let (u , f') = f (hf s qf) in u , λ v → g' (kf s qf) UV (f' v)

    h' : {H J : 2Cont} (α : H →²ᶜ J) (UV : Cont) (s' : appS H UV) → appP J UV (g' α UV s') → appP H UV s'
    h' {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (g + hx + hf + kf) UV (s , f) (qf , v , inj₁ idk) = hf s qf , v , inj₁ let (u , f') = f (hf s qf) in h' (kf s qf) UV (f' v) idk
    h' {S ◃ PX + PF + RF} {T ◃ QX + QF + LF} (g + hx + hf + kf) UV (s , f) (qf , v , inj₂ qx) = hf s qf , v , inj₂ (hx s qx)

  ⊤²ᶜ : 2Cont
  ⊤²ᶜ = ⊤ ◃ (λ _ → ⊥) + (λ _ → ⊥) + λ _ ()

  ⊥²ᶜ : 2Cont
  ⊥²ᶜ = ⊥ ◃ (λ ()) + (λ ()) + λ ()

  _×²ᶜ_ : 2Cont → 2Cont → 2Cont
  (S ◃ PX + PF + RF) ×²ᶜ (T ◃ QX + QF + LF)
    = (S × T)
    ◃ (λ (s , t) → PX s ⊎ QX t)
    + (λ (s , t) → PF s ⊎ QF t)
    + λ{ (s , t) (inj₁ p) → RF s p ; (s , t) (inj₂ q) → LF t q }
-}
