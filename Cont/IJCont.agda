{-# OPTIONS --guardedness #-}
module Cont.IJCont where

open import Data.Product
open import Data.Sum
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding (J; [_])

variable
  X Y Z : Set
  I J K : Set
  A B C : I → Set

{- Containers -}

infix  0 _◃_
record Cont : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Set

⟦_⟧ : Cont → Set → Set
⟦ S ◃ P ⟧ X = Σ[ s ∈ S ] (P s → X)

data W (SP : Cont) : Set where
  sup : ⟦ SP ⟧ (W SP) → W SP


Fam : Set → Set₁
Fam I = I → Set

_→*_ : (A B : I → Set) → Set
_→*_ {I} A B = (i : I) → A i → B i

id* : A →* A
id* i a = a

_∘*_ : B →* C → A →* B → A →* C
(f ∘* g) = λ i a → f i (g i a)
{-# INLINE _∘*_ #-}

record IFunc (I : Set) : Set₁ where
  constructor _,_
  field
    obj : Fam I → Set
    mor : ∀ {A B} → A →* B → obj A → obj B
open IFunc    

_⇒ꟳ_ : IFunc I → IFunc I → Set₁
(F , _) ⇒ꟳ(G , _) = ∀ A → F A → G A

IFunc* : Set → Set → Set₁
IFunc* I J = J → IFunc I

obj* : IFunc* I J → Fam I → Fam J
obj* F A j = F j .obj A

mor* : (F : IFunc* I J) → A →* B → obj* F A →* obj* F B
mor* F f j = F j .mor f

_⇒ꟳ*_ : IFunc* I J → IFunc* I J → Set₁
_⇒ꟳ*_ {I} {J} F G = (A : Fam I) → (j : J) → F j .obj A → G j .obj A

_[_] : ((I ⊎ J → Set) → Set) → ((I → Set) → J → Set) → (I → Set) → Set
(F [ G ]) A = F ([ A , G A ])

{- Indexed containers -}

record ICont (I : Set) : Set₁ where
  constructor _◃_
  field
    S : Set
    P : S → Fam I

I⟦_⟧ : ICont I → Fam I → Set
I⟦ S ◃ P ⟧ A = Σ[ s ∈ S ] (P s →* A)

I⟦_⟧₁ : (SP : ICont I) → A →* B → I⟦ SP ⟧ A → I⟦ SP ⟧ B
I⟦ S ◃ P ⟧₁ g = λ (s , f) → s , g ∘* f
{-# INLINE I⟦_⟧₁ #-}

record ICont* (I J : Set) : Set₁ where
  constructor _◃*_
  field
    S : Fam J
    P : (j : J) → S j → Fam I

⟦_⟧* : ICont* I J → Fam I → Fam J
⟦ S ◃* P ⟧* A j = I⟦ S j ◃ P j ⟧ A

⟦_⟧*₁ : (SP : ICont* I J) → A →* B → ⟦ SP ⟧* A →* ⟦ SP ⟧* B
⟦ SP ⟧*₁ g = λ j → I⟦ SP .ICont*.S j ◃ SP .ICont*.P j ⟧₁ g
{-# INLINE ⟦_⟧*₁ #-}

_[_]ᶜ : ∀ {I J} → ICont (I ⊎ J) → ICont* I J → ICont I
_[_]ᶜ {I} {J} (S ◃ P) (T ◃* Q) = newS ◃ newP
  where
  Pᴵ : S → I → Set
  Pᴵ s i = P s (inj₁ i)

  Pᴶ : S → J → Set
  Pᴶ s j = P s (inj₂ j)

  newS : Set
  newS = I⟦ S ◃ Pᴶ ⟧ T

  newP : newS → Fam I
  newP (s , f) i = Pᴵ s i ⊎ Σ[ j ∈ J ] Σ[ p ∈ Pᴶ s j ] Q j (f j p) i

{- Initial Algbebra -}

data WI (SP : ICont* J J) : Fam J where
  sup : ⟦ SP ⟧* (WI SP) →* WI SP

WIfold : ∀ {SP} → ⟦ SP ⟧* A →* A → WI SP →* A
WIfold {J} {A} {SP} α j (sup .j (s , f)) =
  α j (s , WIfold α ∘* f)

data Path (S : Fam J)
  (Pᴵ : (j : J) → S j → Fam I)
  (Pᴶ : (j : J) → S j → Fam J)
  : (j : J) → WI (S ◃* Pᴶ) j → Fam I where
  path : {i : I} {j : J} {s : S j} {f : Pᴶ j s →* WI (S ◃* Pᴶ)}
    → Pᴵ j s i ⊎ Σ[ j' ∈ J ] Σ[ p ∈ Pᴶ j s j' ] Path S Pᴵ Pᴶ j' (f j' p) i
    → Path S Pᴵ Pᴶ j (sup _ (s , f)) i

{-
pathh : (S : Fam J)
  (Pᴵ : (j : J) → S j → Fam I)
  (Pᴶ : (j : J) → S j → Fam J)
  {i : I} {j : J} {s : S j} {f : Pᴶ j s →* WI (S ◃* Pᴶ)}
  → Pᴵ j s i ⊎ Σ[ j' ∈ J ] Σ[ p ∈ Pᴶ j s j' ] Path S Pᴵ Pᴶ j' (f j' p) i → Path S Pᴵ Pᴶ j (sup _ (s , f)) i
pathh S Pᴵ Pᴶ x = path x
-}

{-
I want to have:
record MI (SP : ICont* J J) : J → Set where
  coinductive
  destructor
    inf : MI SP →* ⟦ SP ⟧* (MI SP)
-}

record MI (SP : ICont* J J) (j : J) : Set where
  coinductive
  field
    inf : ⟦ SP ⟧* (MI SP) j
open MI

{-
I want to have:
record _≈ᴹᴵ_ {j : J} {SP : ICont* J J} : MI SP j → MI SP j → Set where
  coinductive
  open ICont* SP
  destructor
    inf≈ : M₁ ≈ᴹᴵ M₂ → ?
-}


record _≈ᴹᴵ_ {j : J} {SP : ICont* J J} (M₁ M₂ : MI SP j) : Set where
  coinductive
  open ICont* SP
  field
    inf≈ : {s : S j} {f g : P j s →* MI SP}
      → inf M₁ ≡ (s , f) → inf M₂ ≡ (s , g)
      → {j' : J} {p : P j s j'}
      → f j' p ≈ᴹᴵ g j' p
open _≈ᴹᴵ_      

≈ᴹᴵrefl : {j : J} {SP : ICont* J J} {m : MI SP j} → m ≈ᴹᴵ m
inf≈ ≈ᴹᴵrefl refl refl = ≈ᴹᴵrefl

postulate
  MIext : {j : J} {SP : ICont* J J} {m₁ m₂ : MI SP j}
    → m₁ ≈ᴹᴵ m₂ → m₁ ≡ m₂

MIext⁻¹ : {j : J} {SP : ICont* J J} {m₁ m₂ : MI SP j}
  → m₁ ≡ m₂ → m₁ ≈ᴹᴵ m₂
MIext⁻¹ refl = ≈ᴹᴵrefl
  
MIunfold : ∀ {SP} → A →* ⟦ SP ⟧* A → A →* MI SP
inf (MIunfold {J} {A} {SP} α j a) with α j a
... | s , f = s , MIunfold α ∘* f

WI' : ICont* I I → Set
WI' {I} (S ◃* Pᴵ) = W (newS ◃ newP)
  where
  newS : Set
  newS = Σ[ i ∈ I ] S i

  newP : newS → Set
  newP (i , sᵢ) = Σ[ i' ∈ I ] Pᴵ i sᵢ i'
