{-# OPTIONS --guardedness #-}

module Cont.2Cont2 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding (J)

variable X Y : Set

uip : ∀ {ℓ} {A : Set ℓ} {x y : A}
  (p q : x ≡ y) → p ≡ q
uip refl refl = refl

postulate
  funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
    {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

funExt⁻ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
  {f g : (a : A) → B a}
  → f ≡ g
  → (a : A) → f a ≡ g a
funExt⁻ refl a = refl

open import Agda.Primitive

record _≅_ {ℓ} (A B : Set ℓ) : Set (lsuc ℓ) where
  field
    to : A → B
    from : B → A
    to∘from : to ∘ from ≡ id
    from∘to : from ∘ to ≡ id

postulate
  setExt : ∀ {ℓ} {A B : Set ℓ}
    → A ≅ B → A ≡ B
  
setExt⁻ : ∀ {ℓ} {A B : Set ℓ}
  → A ≡ B → A ≅ B
setExt⁻ refl = record { to = id ; from = id ; to∘from = refl ; from∘to = refl }

Σ-≡ :
  ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
  Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂) →
  (a₁ , b₁) ≡ (a₂ , b₂)
Σ-≡ (refl , refl) = refl

{- Containers -}

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set
    
variable
  SP TQ SP' TQ' UV UV' F G : Cont

⟦_⟧ : Cont → Set → Set
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : (SP : Cont) → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g  (s , f) = s , g ∘ f

{- Category of Containers -}

infixr 0 _→ᶜ_
record _→ᶜ_ (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    fS : S → T
    fP : (s : S) → Q (fS s) → P s

⟦_⟧→ᶜ : SP →ᶜ TQ → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
⟦ fS ◃ fP ⟧→ᶜ X (s , f) = fS s , f ∘ fP s

→ᶜ-≡-intro :
  {S T : Set} {P : S → Set} {Q : T → Set}
  {fS fS' : S → T} {fP : (s : S) → Q (fS s) → P s}
  {fP' : (s : S) → Q (fS' s) → P s}
  → (eqfS : fS ≡ fS')
  → (fP ≡ λ s q → fP' s (subst (λ v → Q (v s)) eqfS q))
  → _≡_ {_} {(S ◃ P) →ᶜ (T ◃ Q)} (fS ◃ fP) (fS' ◃ fP')
→ᶜ-≡-intro refl refl = refl

idᶜ : SP →ᶜ SP
idᶜ = id ◃ λ s → id

infixr 9 _∘ᶜ_
_∘ᶜ_ : TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
(g ◃ h) ∘ᶜ (g' ◃ h') = (g ∘ g') ◃ λ s → h' s ∘ h (g' s)

{- WM -}

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

sup⁻ : W SP → ⟦ SP ⟧ (W SP)
sup⁻ (sup (s , f)) = s , f

W₁ : SP →ᶜ TQ → W SP → W TQ
W₁ (g ◃ h) (sup (s , f)) = sup (g s , λ q → W₁ (g ◃ h) (f (h s q)))

module _ (X : Set) (SP : Cont) (g : ⟦ SP ⟧ X → X) where

  foldW : W SP → X
  foldW (sup (s , f)) = g (s , foldW ∘ f)

  commuteW : (sf : ⟦ SP ⟧ (W SP)) → foldW (sup sf) ≡ g (⟦ SP ⟧₁ foldW sf)
  commuteW sf = refl

  !foldW : (foldW' : W SP → X)
    (commuteW' : (sf : ⟦ SP ⟧ (W SP)) → foldW' (sup sf) ≡ g (⟦ SP ⟧₁ foldW' sf))
    → (w : W SP) → foldW' w ≡ foldW w
  !foldW foldW' commuteW' (sup (s , f)) = trans (commuteW' (s , f))
    (cong g (Σ-≡ (refl , funExt λ a → !foldW foldW' commuteW' (f a))))

{- 2nd Order Container -}

record 2Cont : Set₁ where
  inductive
  pattern
  constructor _◃_+_+_
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

variable H J SPPR TQQL : 2Cont

2⟦_⟧T : 2Cont → (Set → Set) → Set → Set
2⟦ S ◃ PX + PF + RF ⟧T F X
  = Σ[ s ∈ S ] (PX s → X × ((pF : PF s) → 2⟦ RF s pF ⟧T F X))

2⟦_⟧T₁ : (H : 2Cont) (F : Set → Set) → (X → Y) → 2⟦ H ⟧T F X → 2⟦ H ⟧T F Y
2⟦ S ◃ PX + PF + RF ⟧T₁ F g (s , f) =
  s , λ pX → let (x , h) = f pX in g x , λ pF → 2⟦ RF s pF ⟧T₁ F g (h pF)

Func : Set₁
Func = Σ[ F ∈ (Set → Set) ] (∀ {X Y} → (X → Y) → F X → F Y)

NatTrans : Func → Func → Set₁
NatTrans (F , F₁) (G , G₁) = (X : Set) → F X → G X

2⟦_⟧F : 2Cont → Func → Func
2⟦ H ⟧F (F , _) = 2⟦ H ⟧T F , 2⟦ H ⟧T₁ F

2⟦_⟧F₁ : (H : 2Cont) → {𝔽 𝔾 : Func} → NatTrans (2⟦ H ⟧F 𝔽) (2⟦ H ⟧F 𝔾)
2⟦ S ◃ PX + PF + RF ⟧F₁ {F , F₁} {G , G₁} X fx = fx .proj₁ , fx .proj₂
