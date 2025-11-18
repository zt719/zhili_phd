{-# OPTIONS --cubical --guardedness #-}

{- Universes -}

open import Agda.Primitive
  using    ( Level ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

variable ℓ ℓ' ℓ'' : Level

{- Interal types -}

open import Agda.Primitive.Cubical
  renaming ( primIMin       to _∧_
           ; primIMax       to _∨_
           ; primINeg       to ~_
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )

{- Path types -}

Path : (A : Type ℓ) → A → A → Type ℓ
Path A a b = PathP (λ _ → A) a b

refl : {A : Type ℓ} {x : A} → Path A x x
refl {x = x} i = x

sym : {A : Type ℓ} {x y : A} → Path A x y → Path A y x
sym p i = p (~ i)

symP : {A : I → Type ℓ} {x : A i0} {y : A i1}
  → PathP (λ i → A i) x y → PathP (λ i → A (~ i)) y x
symP p i = p (~ i)

module _ {A : Type ℓ} {x y : A} {p : Path A x y} where

  ∧-conn : PathP (λ i → Path A x (p i)) refl p
  ∧-conn i j = p (i ∧ j)
  
  --           refl i
  --        x    ⇒    x
  -- refl j ⇓         ⇓ p j
  --        x    ⇒    y
  --            p i
  
  ∨-conn : PathP (λ i → Path A (p i) y) p refl
  ∨-conn i j = p (i ∨ j)
  
  --          p i
  --      x    ⇒     y
  --  p j ⇓          ⇓ refl j
  --      y    ⇒     y
  --         refl i

Square : (A : Type ℓ)
  → {a00 a01 a10 a11 : A}
  → Path A a00 a01 → Path A a10 a11
  → Path A a00 a10 → Path A a01 a11
  → Type ℓ
Square A l r t b = PathP (λ i → Path A (t i) (b i)) l r

SquareP : (A : I → I → Type ℓ)
  → {a00 : A i0 i0} {a01 : A i0 i1} {a10 : A i1 i0} {a11 : A i1 i1}
  → PathP (λ j → A i0 j) a00 a01 → PathP (λ j → A i1 j) a10 a11
  → PathP (λ i → A i i0) a00 a10 → PathP (λ i → A i i1) a01 a11
  → Type ℓ
SquareP A l r t b = PathP (λ i → PathP (λ j → A i j) (t i) (b i)) l r

ap : {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  → {x y : A} → Path A x y
  → Path B (f x) (f y)
ap f p i = f (p i)

apd : {A : Type ℓ} {B : A → Type ℓ'} (f : (x : A) → B x)
  → {x y : A} (p : Path A x y)
  → PathP (λ i → B (p i)) (f x) (f y)
apd f p i = f (p i)

funext : {A : Type ℓ} {B : Type ℓ'}
  → {f g : A → B} → ((x : A) → Path B (f x) (g x))
  → Path (A → B) f g
funext p i x = p x i

funextd : {A : Type ℓ} {B : A → Type ℓ'}
  → {f g : (a : A) → B a} → ((x : A) → Path (B x) (f x) (g x))
  → Path ((x : A) → B x) f g
funextd p i x = p x i

{- Transp -}


subst : {A : Type ℓ} (B : A → Type ℓ')
  → {x y : A} → Path A x y
  → B x → B y
subst B p b = transp (λ i → B (p i)) i0 b

subst-refl : {A : Type ℓ} (B : A → Type ℓ')
  → {x y : A} (b : B x)
  → Path (B x) (subst B refl b) b
subst-refl B {x} b i = transp (λ _ → B x) i b

-- subst B refl b ≐ transp (λ _ → B x) i0 b
--       ⇓
--       b        ≐ transp (λ _ → B x) i1 b

subst-filler : {A : Type ℓ} (B : A → Type ℓ')
  → {x y : A} (p : Path A x y) (b : B x)
  → PathP (λ i → B (p i)) b (subst B p b)
subst-filler B p b j = transp (λ i → B (p (i ∧ j))) (~ j) b

--    b B x    ≐ transp (λ i → B x) i1 b : B x
--      ⇓
-- subst B p b ≐ transp (λ i → B (p i)) i0 b : B y

subst₂ : {A : Type ℓ} {B : A → Type ℓ'} (C : (x : A) → B x → Type ℓ'')
  → {x y : A} (p : Path A x y)
  → {bx : B x} {by : B y} (q : PathP (λ i → B (p i)) bx by)
  → C x bx → C y by
subst₂ C p q c = transp (λ i → C (p i) (q i)) i0 c

transport : {A B : Type ℓ} → Path (Type ℓ) A B → A → B
transport p a = transp (λ i → p i) i0 a

transport-refl : {A : Type ℓ} (x : A) → Path A (transport refl x) x
transport-refl {A = A} x i = transp (λ i → A) i x

transport-filler : {A B : Type ℓ} (p : Path (Type ℓ) A B) (x : A)
  → PathP (λ i → p i) x (transport p x)
transport-filler p x j = transp (λ i → p (i ∧ j)) (~ j) x

J : {A : Type ℓ} (P : (x y : A) → Path A x y → Type ℓ')
  → ((x : A) → P x x refl)
  → (x y : A) (p : Path A x y) → P x y p
J P prefl x y p = transp (λ i → P x (p i) (λ j → p (i ∧ j))) i0 (prefl x)

--     prefl x      : P x x refl
--        ⇓           P ⇓ ⇓  ⇓ 
-- J P prefl x y p  : P x y  p
-- 
-- refl   : Path A x x
-- p      : Path A x y
-- refl2p : PathP (λ i → P x (p i) (λ j → p (i ∧ j))) refl p

{- Partial types -}

open import Cubical.Data.Bool

left-true : (i : I) → Partial (~ i) Bool
left-true i (i = i0) = true

-- true

not-path : (i : I) → Partial (~ i ∨ i) Bool
not-path i (i = i0) = true
not-path i (i = i1) = false

-- true      false


{- Extension types -}

open import Agda.Builtin.Cubical.Sub public
  renaming (primSubOut to outS)

_[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
A [ φ ↦ u ] = Sub A φ u

infix 4 _[_↦_]

refl-extends : (i : I) → Bool [ ~ i ↦ left-true i ]
refl-extends i = inS (refl {x = true} i)

not-extensible : ((i : I) → Bool [ (~ i ∨ i) ↦ not-path i ])
  → Path Bool true false
not-extensible ext i = outS (ext i)

{- Σ types -}

open import Agda.Builtin.Sigma
infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

{- Composition -}

module _ {A : Type ℓ} {w x y z : A} (p : Path A w x) (q : Path A x y) (r : Path A y z) where
  
  shape : (i j : I) → Partial (~ i ∨ i ∨ ~ j) A
  shape i j (i = i0) = p (~ j)
  shape i j (i = i1) = r j
  shape i j (j = i0) = q i  

  --           q i
  --         x  →  y
  -- p (~ j) ↓     ↓ r j
  --         w     x
  
--  composite : Path A w z
--  composite i = hcomp {!!} {!!}


{- Glue types -}

open import Agda.Builtin.Cubical.Glue

Glue : (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
       → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

unglue : {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
         {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}

{- Univalence -}

id : {A : Type ℓ} → A → A
id x = x

idEquiv : {A : Type ℓ} → A ≃ A
idEquiv = id , record { equiv-proof = λ x → (x , refl) , λ{ (y , p) i → p (~ i) , λ j → p (~ i ∨ j) } }

ua : {A B : Type ℓ} → A ≃ B → Path (Type ℓ) A B
ua {ℓ} {A} {B} e i = Glue B {~ i ∨ i} λ{ (i = i0) → A , e ; (i = i1) → B , idEquiv }

-- open import Cubical.Foundations.Univalence
