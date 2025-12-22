{-# OPTIONS --guardedness #-}

open import Data.Sum
open import Data.Product

record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

variable F G : Cont

record ⟦_⟧ (SP : Cont) (X : Set) : Set where
  constructor _,_
  open Cont SP
  field
    s : S
    f : P s → S
  
data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP

record _→ᶜ_ (SP TQ : Cont) : Set where
  constructor _◃_
  open Cont SP
  open Cont TQ renaming (S to T; P to Q)
  field
    g : S → T
    h : (s : S) → Q (g s) → P s

record 2Cont : Set₁ where
  inductive
  pattern
  constructor _◃_+_+_
  field
    S : Set
    PX : S → Set
    PF : S → Set
    RF : (s : S) → PF s → 2Cont

2⟦_⟧S' : (H : 2Cont) (T : Set) (Q : T → Set) → Set
2⟦_⟧S' (S ◃ PX + PF + RF) T Q
  = Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ T ] (Q t → 2⟦ RF s pf ⟧S' T Q))

2⟦_⟧P' : (H : 2Cont) (T : Set) (Q : T → Set) → 2⟦ H ⟧S' T Q → Set
2⟦ S ◃ PX + PF + RF ⟧P' T Q (s , f) = Σ[ pf ∈ PF s ] let (t , g) = f pf in Σ[ q ∈ Q t ] (2⟦ RF s pf ⟧P' T Q (g q) ⊎ PX s)

2⟦_⟧S : (H : 2Cont) (TQ : Cont) → Set
2⟦ H ⟧S (T ◃ Q) = 2⟦ H ⟧S' T Q

2⟦_⟧P : (H : 2Cont) (TQ : Cont) → 2⟦ H ⟧S TQ → Set
2⟦ H ⟧P (T ◃ Q) = 2⟦ H ⟧P' T Q

2⟦_⟧ : 2Cont → Cont → Cont
2⟦ H ⟧ F = 2⟦ H ⟧S F ◃ 2⟦ H ⟧P F

2⟦_⟧S₁ : (H : 2Cont) → F →ᶜ G → 2⟦ H ⟧S F → 2⟦ H ⟧S G
2⟦_⟧S₁ (S ◃ PX + PF + RF) (g ◃ h) (s , f)
  = s , λ pf → let (t , f') = f pf in
    g t , λ u → 2⟦ RF s pf ⟧S₁ (g ◃ h) (f' (h t u))

2⟦_⟧P₁ : (H : 2Cont) (f : F →ᶜ G) (s : 2⟦ H ⟧S F) → 2⟦ H ⟧P G (2⟦ H ⟧S₁ f s) → 2⟦ H ⟧P F s
2⟦ S ◃ PX + PF + RF ⟧P₁ (g ◃ h) (s , f) (pf , (u , inj₁ p'))
  = let (t , f') = f pf in pf , (h t u , inj₁ (2⟦ RF s pf ⟧P₁ (g ◃ h) (f' (h t u)) p'))
2⟦ S ◃ PX + PF + RF ⟧P₁ (g ◃ h) (s , f) (pf , (u , inj₂ px))
  = let (t , f') = f pf in (pf , (h t u , inj₂ px))

2⟦_⟧₁ : (H : 2Cont) → F →ᶜ G → 2⟦ H ⟧ F →ᶜ 2⟦ H ⟧ G
2⟦ H ⟧₁ F = 2⟦ H ⟧S₁ F ◃ 2⟦ H ⟧P₁ F

data 2WS' (H H' : 2Cont) : Set
2WP' : (H H' : 2Cont) → 2WS' H H' → Set

data 2WS' H H' where
  2supS' : (open 2Cont H') →
    Σ[ s ∈ S ] ((pf : PF s) → Σ[ t ∈ 2WS' H H ] (2WP' H H t → 2WS' H (RF s pf))) →
    2WS' H H'

2WP' H (S ◃ PX + PF + RF) (2supS' (s , f))
  = Σ[ pf ∈ PF s ] let (t , g) = f pf in
    Σ[ q ∈ 2WP' H H t ] (2WP' H (RF s pf) (g q) ⊎ PX s)

2WS : 2Cont → Set
2WS H = 2WS' H H

2WP : (H : 2Cont) → 2WS H → Set
2WP H = 2WP' H H

2W : 2Cont → Cont
2W H = 2WS H ◃ 2WP H

2supS : {H H' : 2Cont} → 2⟦ H' ⟧S (2W H) → 2WS' H H'
2supS {H} {S ◃ PX + PF + RF} (s , f) =
  2supS' (s , λ pf → let (t , g) = f pf in (t , λ q → 2supS (g q)))

2supP : {H H' : 2Cont} (s : 2⟦ H' ⟧S (2W H))
  → 2WP' H H' (2supS s) → 2⟦ H' ⟧P (2W H) s
2supP {H} {S ◃ PX + PF + RF} (s , f) (pf , q , inj₁ r) =
  let (t , g) = f pf in (pf , q , inj₁ (2supP (g q) r))
2supP {H} {S ◃ PX + PF + RF} (s , f) (pf , q , inj₂ px) =
  (pf , q , inj₂ px)

2sup : {H : 2Cont} → 2⟦ H ⟧ (2W H) →ᶜ 2W H
2sup = 2supS ◃ 2supP

{- LListᶜ Example -}

data LList (X : Set) : Set where
  [] : LList X
  _∷_ : X → LList (LList X) → LList X

open import Data.Unit
open import Data.Empty

data S : Set

P : S → Set

data S where
  leaf : S
  node : (s : S) (f : P s → S) → S

P leaf = ⊥
P (node s f) = ⊤ ⊎ Σ[ p ∈ P s ] P (f p)

LListᶜ : Cont
LListᶜ = S ◃ P

-- H F X = ⊤ ⊎ F (F X)
H²ᶜ : 2Cont
H²ᶜ = (⊤ ⊎ ⊤) ◃ (λ{ (inj₁ tt) → ⊥ ; (inj₂ tt) → ⊥ })
  + (λ{ (inj₁ tt) → ⊥ ; (inj₂ tt) → ⊤ })
  + λ{ (inj₂ tt) tt → FXᶜ }
  where
  FXᶜ : 2Cont
  FXᶜ = ⊤ ◃ (λ{ tt → ⊥ }) + (λ{ tt → ⊤ }) + λ{ tt tt → Xᶜ }
    where
    Xᶜ : 2Cont
    Xᶜ = ⊤ ◃ (λ{ tt → ⊤ }) + (λ{ tt → ⊥ }) + λ{ tt () }

open import Relation.Binary.PropositionalEquality

record _≃_ {ℓ} (A B : Set ℓ) : Set ℓ where
  field
    to   : A → B
    from : B → A
    to-from : ∀ b → to (from b) ≡ b
    from-to : ∀ a → from (to a) ≡ a

postulate
  ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
  funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
    → {f g : (a : A) → B a}
    → ((a : A) → f a ≡ g a)
    → f ≡ g

eqᶜ : {S T : Set} (eq : S ≡ T)
  → {P : S → Set} {Q : T → Set}
  → P ≡ (λ s → Q (subst (λ S → S) eq s))
  → _≡_ {A = Cont} (S ◃ P) (T ◃ Q)
eqᶜ refl refl = refl

toS : 2WS H²ᶜ → S
fromS : S → 2WS H²ᶜ
eqS : 2WS H²ᶜ ≡ S

toP : (s : 2WS H²ᶜ) → 2WP H²ᶜ s → P (subst (λ S → S) eqS s)
fromP : (s : 2WS H²ᶜ) → P (subst (λ S → S) eqS s) → 2WP H²ᶜ s
eqP : 2WP H²ᶜ ≡ (λ s → P (subst (λ S → S) eqS s))

toS (2supS' (inj₁ tt , _)) = leaf
toS (2supS' (inj₂ tt , f)) =
  let (t , g) = f tt in node (toS t) (λ p → {!g!})

fromS = {!!}

toP = {!!}

fromP = {!!}

eqS = ua (record { to = toS ; from = fromS ; to-from = {!!} ; from-to = {!!} })
eqP = funExt (λ s → ua (record { to = toP s ; from = fromP s ; to-from = {!!} ; from-to = {!!} }))

proof : 2W H²ᶜ ≡ LListᶜ
proof = eqᶜ eqS eqP
