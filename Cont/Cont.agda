module Cont.Cont where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding (J; [_])

private variable
  I J K : Set
  A B C : I → Set  
  X Y Z : Set

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
  SP TQ SP' TQ' UV UV' : Cont

⟦_⟧ : Cont → Set → Set
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : (SP : Cont) → (X → Y) → ⟦ SP ⟧ X → ⟦ SP ⟧ Y
⟦ SP ⟧₁ g (s , f) = s , g ∘ f

⟦_⟧-id : (SP : Cont) → ⟦ SP ⟧₁ (id {A = X}) ≡ id
⟦ SP ⟧-id = refl

⟦_⟧-∘ : (SP : Cont) {f : Y → Z} {g : X → Y}
  → ⟦ SP ⟧₁ (f ∘ g) ≡ ⟦ SP ⟧₁ f ∘ ⟦ SP ⟧₁ g
⟦ SP ⟧-∘ = refl

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

⟦_⟧→ᶜ-nat : (α : SP →ᶜ TQ) (f : X → Y)
  → ⟦ α ⟧→ᶜ Y ∘ ⟦ SP ⟧₁ f ≡ ⟦ TQ ⟧₁ f ∘ ⟦ α ⟧→ᶜ X
⟦ fS ◃ fP ⟧→ᶜ-nat f = refl

module fullyfaithful where

  →ᶜ-≡ : {S : Set} {P : S → Set} {T : Set} {Q : T → Set}
    → {fS fS' : S → T} {fP : (s : S) → Q (fS s) → P s}
    → {fP' : (s : S) → Q (fS' s) → P s}
    → (fS-eq : fS ≡ fS')
    → (fP-eq : fP ≡ λ s q → fP' s (subst Q (funExt⁻ fS-eq s) q))
    → _≡_ {A = (S ◃ P) →ᶜ (T ◃ Q)} (fS ◃ fP) (fS' ◃ fP')
  →ᶜ-≡ refl refl = refl

  to : SP →ᶜ TQ → (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X
  to = ⟦_⟧→ᶜ

{-
  faith : (α β : SP →ᶜ TQ)
    → ((X : Set) (sf : ⟦ SP ⟧ X) → to α X sf ≡ to β X sf)
    → α ≡ β
  faith (fS ◃ fP) (fS' ◃ fP') p = →ᶜ-≡ {!!} {!!}
-}

  from : ((X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X) → SP →ᶜ TQ
  from {S ◃ P} {T ◃ Q} η = 
    (λ s → η (P s) (s , id) .proj₁)
    ◃ λ s → η (P s) (s , id) .proj₂

  from∘to : (α : SP →ᶜ TQ) → from (to α) ≡ α
  from∘to α = refl

{-
  to∘from : (η : (X : Set) → ⟦ SP ⟧ X → ⟦ TQ ⟧ X) → to (from η) ≡ η
  to∘from {S ◃ P} {T ◃ Q} η = funExt λ X → funExt λ{ (s , f) → Σ-≡ ({!!} , {!!})}
-}

idᶜ : SP →ᶜ SP
idᶜ = id ◃ λ s → id

infixr 9 _∘ᶜ_
_∘ᶜ_ : TQ →ᶜ UV → SP →ᶜ TQ → SP →ᶜ UV
(g ◃ h) ∘ᶜ (g' ◃ h') = (g ∘ g') ◃ λ s → h' s ∘ h (g' s)

⊤ᶜ : Cont
⊤ᶜ = ⊤ ◃ λ _ → ⊥

⊥ᶜ : Cont
⊥ᶜ = ⊥ ◃ λ ()

infixr 2 _×ᶜ_
_×ᶜ_ : Cont → Cont → Cont
(S ◃ P) ×ᶜ (T ◃ Q) = S × T ◃ λ (s , t) → P s ⊎ Q t

_×ᶜ₁_ : SP →ᶜ TQ → SP' →ᶜ TQ' → SP ×ᶜ SP' →ᶜ TQ ×ᶜ TQ'
(g ◃ h) ×ᶜ₁ (g' ◃ h')
  = (λ (s , s') → g s , g' s')
  ◃ λ{ (s , s') (inj₁ p) → inj₁ (h s p) ; (s , s') (inj₂ p') → inj₂ (h' s' p') }

infixr 1 _⊎ᶜ_
_⊎ᶜ_ : Cont → Cont → Cont
(S ◃ P) ⊎ᶜ (T ◃ Q) = S ⊎ T ◃ λ{ (inj₁ s) → P s ; (inj₂ t) → Q t }

_⊎ᶜ₁_ : SP →ᶜ TQ → SP' →ᶜ TQ' → SP ⊎ᶜ SP' →ᶜ TQ ⊎ᶜ TQ'
(g ◃ h) ⊎ᶜ₁ (g' ◃ h')
  = (λ{ (inj₁ s) → inj₁ (g s) ; (inj₂ s') → inj₂ (g' s') })
  ◃ λ{ (inj₁ s) p → h s p ; (inj₂ s') p' → h' s' p' }

Πᶜ : (I : Set) (f : I → Cont) → Cont
Πᶜ I fs = ((i : I) → let S ◃ P = fs i in S)
  ◃ λ f → Σ[ i ∈ I ] let S ◃ P = fs i in P (f i)

infix 2 Πᶜ-syntax

Πᶜ-syntax : (I : Set) (f : I → Cont) → Cont
Πᶜ-syntax = Πᶜ

syntax Πᶜ-syntax A (λ x → B) = Πᶜ[ x ∈ A ] B

Πᶜ₁ : (I : Set) {SPs TQs : I → Cont}
  → ((i : I) → SPs i →ᶜ TQs i) → Πᶜ I SPs →ᶜ Πᶜ I TQs
Πᶜ₁ I f = (λ s i → let g ◃ h = f i in g (s i))
  ◃ λ s (i , p) → i , let g ◃ h = f i in h (s i) p

Σᶜ : (I : Set) (f : I → Cont) → Cont
Σᶜ I fs = (Σ[ i ∈ I ] let S ◃ P = fs i in S)
  ◃ λ (i , s) → let S ◃ P = fs i in P s

infix 2 Σᶜ-syntax

Σᶜ-syntax : (I : Set) → (I → Cont) → Cont
Σᶜ-syntax = Σᶜ

syntax Σᶜ-syntax A (λ x → B) = Σᶜ[ x ∈ A ] B

Σᶜ₁ : (I : Set) {SPs TQs : I → Cont}
  → ((i : I) → SPs i →ᶜ TQs i) → Σᶜ I SPs →ᶜ Σᶜ I TQs
Σᶜ₁ I f = (λ (i , s) → i , let g ◃ h = f i in g s)
  ◃ λ (i , s) p → let g ◃ h = f i in h s p

!ᶜ : (SP : Cont) → ⊥ᶜ →ᶜ SP
!ᶜ (S ◃ P) = (λ ()) ◃ λ ()

¿ᶜ : (SP : Cont) → SP →ᶜ ⊤ᶜ
¿ᶜ (S ◃ P) = (λ _ → tt) ◃ λ s ()

proj₁ᶜ : SP ×ᶜ TQ →ᶜ SP
proj₁ᶜ = proj₁ ◃ λ{ (S , T) p → inj₁ p }

proj₂ᶜ : SP ×ᶜ TQ →ᶜ TQ
proj₂ᶜ = proj₂ ◃ λ{ (S , T) q → inj₂ q }

<_,_>ᶜ : SP →ᶜ TQ → SP →ᶜ TQ' → SP →ᶜ TQ ×ᶜ TQ'
< f ◃ g , f' ◃ g' >ᶜ = < f , f' > ◃ λ{ s (inj₁ p) → g s p ; s (inj₂ q) → g' s q }

inj₁ᶜ : SP →ᶜ SP ⊎ᶜ TQ

inj₁ᶜ = inj₁ ◃ λ s p → p

inj₂ᶜ : TQ →ᶜ SP ⊎ᶜ TQ
inj₂ᶜ = inj₂ ◃ λ s q → q

[_,_]ᶜ : SP →ᶜ TQ → SP' →ᶜ TQ → SP ⊎ᶜ SP' →ᶜ TQ
[ f ◃ g , f' ◃ g' ]ᶜ = [ f , f' ] ◃ λ{ (inj₁ s) p → g s p ; (inj₂ s') q → g' s' q }

{- Semiring -}

lunit⊎ᶜ : ⊥ᶜ ⊎ᶜ SP →ᶜ SP
lunit⊎ᶜ = (λ{ (inj₂ s) → s }) ◃ λ{ (inj₂ s) p → p }

runit⊎ᶜ : SP ⊎ᶜ ⊥ᶜ →ᶜ SP
runit⊎ᶜ = (λ{ (inj₁ s) → s }) ◃ λ{ (inj₁ s) p → p }

comm⊎ᶜ : SP ⊎ᶜ TQ →ᶜ TQ ⊎ᶜ SP
comm⊎ᶜ = (λ{ (inj₁ s) → inj₂ s ; (inj₂ t) → inj₁ t }) ◃ λ{ (inj₁ t) q → q ; (inj₂ s) p → p }

assoc⊎ᶜ : (SP ⊎ᶜ TQ) ⊎ᶜ UV →ᶜ SP ⊎ᶜ (TQ ⊎ᶜ UV)
assoc⊎ᶜ = (λ{ (inj₁ (inj₁ s)) → inj₁ s ; (inj₁ (inj₂ t)) → inj₂ (inj₁ t) ; (inj₂ u) → inj₂ (inj₂ u) })
  ◃ λ{ (inj₁ (inj₁ s)) p → p ; (inj₁ (inj₂ t)) q → q ; (inj₂ u) v → v }

lunit×ᶜ : ⊤ᶜ ×ᶜ SP →ᶜ SP
lunit×ᶜ = (λ (tt , s) → s) ◃ λ (tt , s) p → inj₂ p

runit×ᶜ : SP ×ᶜ ⊤ᶜ →ᶜ SP
runit×ᶜ = (λ (s , tt) → s) ◃ λ (s , tt) p → inj₁ p

comm×ᶜ : SP ×ᶜ TQ →ᶜ TQ ×ᶜ SP
comm×ᶜ = (λ (s , t) → t , s) ◃ λ{ (s , t) (inj₁ q) → inj₂ q ; (s , t) (inj₂ p) → inj₁ p }

assoc×ᶜ : (SP ×ᶜ TQ) ×ᶜ UV →ᶜ SP ×ᶜ (TQ ×ᶜ UV)
assoc×ᶜ = (λ ((s , t) , u) → s , t , u)
  ◃ λ{ ((s , t) , u) (inj₁ p) → inj₁ (inj₁ p) ; ((s , t) , u) (inj₂ (inj₁ q)) → inj₁ (inj₂ q) ; ((s , t) , u) (inj₂ (inj₂ v)) → inj₂ v }

labsᶜ : ⊥ᶜ ×ᶜ SP →ᶜ ⊥ᶜ
labsᶜ = (λ ()) ◃ λ ()

rabsᶜ : SP ×ᶜ ⊥ᶜ →ᶜ ⊥ᶜ
rabsᶜ = (λ ()) ◃ λ ()

ldistrᶜ : SP ×ᶜ (TQ ⊎ᶜ UV) →ᶜ SP ×ᶜ TQ ⊎ᶜ SP ×ᶜ UV
ldistrᶜ = (λ{ (s , inj₁ t) → inj₁ (s , t) ; (s , inj₂ u) → inj₂ (s , u) })
        ◃ λ{ (s , inj₁ t) (inj₁ p) → inj₁ p ; (s , inj₁ t) (inj₂ q) → inj₂ q
           ; (s , inj₂ u) (inj₁ p) → inj₁ p ; (s , inj₂ u) (inj₂ v) → inj₂ v }

rdistrᶜ : (SP ⊎ᶜ TQ) ×ᶜ UV →ᶜ SP ×ᶜ UV ⊎ᶜ TQ ×ᶜ UV
rdistrᶜ = (λ{ (inj₁ s , u) → inj₁ (s , u) ; (inj₂ t , u) → inj₂ (t , u) })
        ◃ λ{ (inj₁ s , u) (inj₁ p) → inj₁ p ; (inj₁ s , u) (inj₂ v) → inj₂ v
           ; (inj₂ t , u) (inj₁ q) → inj₁ q ; (inj₂ t , u) (inj₂ v) → inj₂ v }

{- Infinitary Commutative Semiring -}

module _ (I : Set) (J : I → Set) (C : (i : I) → J i → Cont) where

  assocΣᶜ : Σᶜ[ (i , j) ∈ Σ I J ] C i j →ᶜ Σᶜ[ i ∈ I ] Σᶜ[ j ∈ J i ] C i j
  assocΣᶜ = (λ ((i , j) , c) → i , j , c) ◃ λ s p → p

  curryᶜ : Πᶜ[ (i , j) ∈ Σ I J ] C i j →ᶜ Πᶜ[ i ∈ I ] Πᶜ[ j ∈ J i ] C i j
  curryᶜ = (λ c i j → c (i , j)) ◃ λ s (i , j , c) → (i , j) , c

  choiceᶜ : Σᶜ[ f ∈ ((i : I) → J i) ] Πᶜ[ i ∈ I ] C i (f i) →ᶜ Πᶜ[ i ∈ I ] Σᶜ[ j ∈ J i ] C i j
  choiceᶜ = (λ (f , g) i → f i , g i) ◃ λ s p → p

{- Container Functor Composition -}

Iᶜ : Cont
Iᶜ = ⊤ ◃ λ{ tt → ⊤ }

infixr 3 _⊗ᶜ_

_⊗ᶜ_ : Cont → Cont → Cont
(S ◃ P) ⊗ᶜ (T ◃ Q) = (Σ[ s ∈ S ] (P s → T)) ◃ λ (s , f) → Σ[ p ∈ P s ] Q (f p)

_⊗ᶜ₁_ : SP →ᶜ TQ → SP' →ᶜ TQ' → SP ⊗ᶜ SP' →ᶜ TQ ⊗ᶜ TQ'
(g ◃ h) ⊗ᶜ₁ (g' ◃ h') = (λ (s , f) → g s , g' ∘ f ∘ h s)
  ◃ λ{ (s , f) (q , q') → h s q , h' (f (h s q)) q' }

λᶜ : Iᶜ ⊗ᶜ SP →ᶜ SP
λᶜ = (λ (tt , f) → f tt) ◃ λ (tt , f) p → tt , p

λ⁻ᶜ : SP →ᶜ Iᶜ ⊗ᶜ SP
λ⁻ᶜ = (λ s → tt , λ _ → s) ◃ λ s (tt , p) → p

ρᶜ : SP ⊗ᶜ Iᶜ →ᶜ SP
ρᶜ = (λ (s , _) → s) ◃ λ (s , _) p → p , tt

ρ⁻ᶜ : SP →ᶜ SP ⊗ᶜ Iᶜ
ρ⁻ᶜ = (λ s → s , λ _ → tt) ◃ λ s (p , tt) → p

αᶜ : (SP ⊗ᶜ TQ) ⊗ᶜ UV →ᶜ SP ⊗ᶜ (TQ ⊗ᶜ UV)
αᶜ = (λ ((s , f) , g) → s , λ p → (f p , λ q → g (p , q)))
   ◃ λ ((s , f) , g) (p , (q , v)) → ((p , q) , v)

α⁻ᶜ : SP ⊗ᶜ (TQ ⊗ᶜ UV) →ᶜ (SP ⊗ᶜ TQ) ⊗ᶜ UV
α⁻ᶜ = (λ{ (s , f) → (s , λ p → let (t , g) = f p in t) , λ (p , q) → let (t , g) = f p in g q })
     ◃ λ (s , f) ((p , q) , v) → (p , (q , v))

{- Finitary Compositions -}

open import Data.Nat
open import Data.Fin

⨂ᶜ : {n : ℕ} → (Fin n → Cont) → Cont
⨂ᶜ f = ⨂ᶜS f ◃ ⨂ᶜP f
  where
  ⨂ᶜS : {n : ℕ} → (Fin n → Cont) → Set
  ⨂ᶜS {zero} f = ⊤
  ⨂ᶜS {suc n} f with f zero
  ... | S ◃ P = Σ[ s ∈ S ] (P s → ⨂ᶜS {n} (f ∘ suc))

  ⨂ᶜP : {n : ℕ} (f : Fin n → Cont) → ⨂ᶜS {n} f → Set
  ⨂ᶜP {zero} f tt = ⊤
  ⨂ᶜP {suc n} f (s , g) with f zero
  ... | S ◃ P = Σ[ p ∈ P s ] ⨂ᶜP {n} (f ∘ suc) (g p)
