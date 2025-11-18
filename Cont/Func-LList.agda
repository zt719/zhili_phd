{-# OPTIONS --guardedness #-}

module Cont.Func-LList where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Cont.Cont

{- Some Tools -}

funExt⁻ : {A : Set} {B : A → Set} {f g : (x : A) → B x}
  → f ≡ g
  → (x : A) → f x ≡ g x
funExt⁻ refl x = refl

postulate
  funExt : {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x)
    → f ≡ g

  funExt⁻∘funExt : {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → id ≡ funExt⁻ {A} {B} {f} {g} ∘ funExt

funExt₂ : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
  → {f g : (x : A) (y : B x) → C x y}
  → ((x : A) (y : B x) → f x y ≡ g x y)
  → f ≡ g
funExt₂ h = funExt λ x → funExt λ y → h x y

Eq→ᶜ : {S : Set} {P : S → Set} {T : Set} {Q : T → Set}
  → {g g' : S → T} {h : (s : S) → Q (g s) → P s} {h' : (s : S) → Q (g' s) → P s}
  → (Σ[ eq ∈ g ≡ g' ] h ≡ λ s x → h' s (subst Q (funExt⁻ eq s) x))
  → _≡_ {A = (S ◃ P) →ᶜ (T ◃ Q)} (g ◃ h) (g' ◃ h')
Eq→ᶜ (refl , refl) = refl

{- H as a signature of Functor of LList -}

data LList (X : Set) : Set where
  [] : LList X
  _∷_ : X → LList (LList X) → LList X

H : (Set → Set) → Set → Set
H F X = ⊤ ⊎ X × F (F X)

HS : Cont → Set
HP : (SP : Cont) → HS SP → Set

HS (S ◃ P) = ⊤ ⊎ Σ[ s ∈ S ] (P s → S)

HP (S ◃ P) (inj₁ tt) = ⊥
HP (S ◃ P) (inj₂ (s , f)) = ⊤ ⊎ Σ[ p ∈ P s ] P (f p)

ℍ : Cont → Cont
ℍ SP = HS SP ◃ HP SP

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
  h' (inj₂ (s , f)) (inj₂ (p , pfp)) = inj₂ (h s p , h (f (h s p)) pfp)

data S : Set

P : S → Set

data S where
  leaf : S
  node : (s : S) (f : P s → S) → S

P leaf = ⊥
P (node s f) = ⊤ ⊎ Σ[ p ∈ P s ] P (f p)

S' : Set
S' = ⊤ ⊎ Σ[ s ∈ S ] (P s → S)

P' : S' → Set
P' (inj₁ tt) = ⊥
P' (inj₂ (s , f)) = ⊤ ⊎ Σ[ p ∈ P s ] P (f p)

inS : S' → S
inS (inj₁ tt) = leaf
inS (inj₂ (s , f)) = node s f

inP : (s' : S') → P (inS s') → P' s'
inP (inj₂ (s , f)) (inj₁ tt) = inj₁ tt
inP (inj₂ (s , f)) (inj₂ (p , pfq)) = inj₂ (p , pfq)

inSP : (S' ◃ P') →ᶜ (S ◃ P)
inSP = inS ◃ inP

module _ (T : Set) (Q : T → Set) where

  T' : Set
  T' = ⊤ ⊎ Σ[ t ∈ T ] (Q t → T)

  Q' : T' → Set
  Q' (inj₁ tt) = ⊥
  Q' (inj₂ (t , f)) = ⊤ ⊎ Σ[ q ∈ Q t ] Q (f q)

  module _ (inT : T' → T) (inQ : (t' : T') → Q (inT t') → Q' t') where

    inTQ : (T' ◃ Q') →ᶜ (T ◃ Q)
    inTQ = inT ◃ inQ

    {- mutual : foldS foldP -}
    foldS : S → T
    foldP : (s : S) → Q (foldS s) → P s

    foldS leaf = inT (inj₁ tt)
    foldS (node s f) = inT (inj₂ (foldS s , foldS ∘ f ∘ foldP s))

    foldP leaf q with inQ (inj₁ tt) q
    ... | ()
    foldP (node s f) q with inQ (inj₂ (foldS s , foldS ∘ f ∘ foldP s)) q
    ... | inj₁ tt = inj₁ tt
    ... | inj₂ (q , qfq) = inj₂ (foldP s q , foldP (f (foldP s q)) qfq)

    foldSP : (S ◃ P) →ᶜ (T ◃ Q) 
    foldSP = foldS ◃ foldP

    H-foldS : S' → T'
    H-foldS (inj₁ tt) = inj₁ tt
    H-foldS (inj₂ (s , f)) = inj₂ (foldS s , foldS ∘ f ∘ foldP s)

    H-foldP : (s' : S') → Q' (H-foldS s') → P' s'
    H-foldP (inj₂ (s , f)) (inj₁ tt) = inj₁ tt
    H-foldP (inj₂ (s , f)) (inj₂ (q , qfq)) = inj₂ (foldP s q , foldP (f (foldP s q)) qfq)

    H-foldSP : (S' ◃ P') →ᶜ (T' ◃ Q')
    H-foldSP = H-foldS ◃ H-foldP

    commuteS : (s' : S') → foldS (inS s') ≡ inT (H-foldS s')
    commuteS (inj₁ tt) = refl
    commuteS (inj₂ (s , f)) = refl

    commuteP : (s' : S') (q : Q (foldS (inS s')))
      → inP s' (foldP (inS s') q)
      ≡ H-foldP s' (inQ (H-foldS s') (subst Q (commuteS s') q))
    commuteP (inj₁ tt) q = refl
    commuteP (inj₂ (s , f)) q with inQ (inj₂ (foldS s , foldS ∘ f ∘ foldP s)) q
    ... | inj₁ tt = refl
    ... | inj₂ (q , qfq) = refl
    
    commuteSP : foldSP ∘ᶜ inSP ≡ inTQ ∘ᶜ H-foldSP
    commuteSP = Eq→ᶜ
      ( funExt commuteS
      , funExt₂ λ s' q → trans (commuteP s' q)
        (cong (λ x → H-foldP s' (inQ (H-foldS s') (subst Q x q)))
        (funExt⁻ (funExt⁻ funExt⁻∘funExt commuteS) s'))
      )

-- commuteS :                   commuteP :
--  
--        H-foldS                      H-foldP
--     S'    →    T'                P'    ←    Q'
--
-- inS ↓          ↓ inT         inP ↑          ↑ inQ
--
--     S     →    T                 P     ←    Q
--         foldS                        foldP
