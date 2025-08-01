{-# OPTIONS --cubical --guardedness #-}

module DTLC where

open import Cubical.Foundations.Prelude hiding (_,_)

{- Sorts -}
data UU : Set
data EL : UU → Set

data UU where
  con : UU
  ty  : EL con → UU
  tms : EL con → EL con → UU
  tm  : (Γ : EL con) → EL (ty Γ)  → UU

Con : Set
Con = EL con

variable Γ Δ Θ : Con

Ty : Con → Set
Ty Γ = EL (ty Γ)

variable A B C : Ty Γ

Tms : Con → Con → Set
Tms Δ Γ = EL (tms Δ Γ)

variable γ δ θ : Tms Δ Γ

Tm : (Γ : Con) → Ty Γ → Set
Tm Γ A = EL (tm Γ A)

variable t u : Tm Γ A

{- Heterogeneous Equatity for Tm -}
infix 2 _≡[_]≡_
_≡[_]≡_ : Tm Γ A → A ≡ B → Tm Γ B → Set
t ≡[ p ]≡ u = PathP (λ i → Tm _ (p i)) t u

{- Lifting Coerces for Tm -}
TmΓ≡ : A ≡ B → Tm Γ A → Tm Γ B
TmΓ≡ {Γ} p = transport (cong (Tm Γ) p)

infixl 5 _▹_
infixr 5 _,_
infixr 9 _∘_

{-# NO_POSITIVITY_CHECK #-}
data EL where

  {- Category ℂ - Context & Substitution -}
  id   : Tms Γ Γ
  _∘_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  ass  : (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
  idl  : id ∘ γ ≡ γ
  idr  : γ ∘ id ≡ γ

  {- Presheaf 𝐓 - Term & Type -}
  _[_]T : Ty Γ → Tms Δ Γ → Ty Δ
  [id]T : A [ id ]T ≡ A
  [∘]T  : A [ γ ∘ δ ]T ≡ A [ γ ]T [ δ ]T

  _[_]t : Tm Γ A → (γ : Tms Δ Γ) → Tm Δ (A [ γ ]T)
  
  {- Terminal Obejct ∙ - Empty Substitution -}
  ∙    : Con
  ε    : Tms Γ ∙
  εη   : γ ≡ ε

  {- Context Comprehension -}
  _▹_  : (Γ : Con) → Ty Γ → Con
  _,_  : (γ : Tms Δ Γ) → Tm Δ (A [ γ ]T) → Tms Δ (Γ ▹ A)
  π₁   : Tms Δ (Γ ▹ A) → Tms Δ Γ
  π₂   : (γ : Tms Δ (Γ ▹ A)) → Tm Δ (A [ π₁ γ ]T)
  
  π₁β : π₁ (γ , t) ≡ γ
  π₂β : TmΓ≡ (cong (A [_]T) π₁β) (π₂ (γ , t)) ≡ t
  -- π₂β : π₂ (γ , t) ≡ TmΓ≡ (sym (cong (A [_]T) π₁β)) t  
  -- π₂β : π₂ (γ , t) ≡[ cong (A [_]T) π₁β ]≡ t
    
  πη  : π₁ γ , π₂ γ ≡ γ
  ,∘  : (δ , t) ∘ γ ≡ δ ∘ γ , TmΓ≡ (sym [∘]T) (t [ γ ]t)  

  _↑_  : (γ : Tms Δ Γ) (A : Ty Γ) → Tms (Δ ▹ (A [ γ ]T)) (Γ ▹ A)
  ↑≡   : γ ↑ A ≡ γ ∘ π₁ id , TmΓ≡ (sym [∘]T) (π₂ id)

  {- Dependent Function Types -}
  Π    : Ty Γ → Ty (Γ ▹ A) → Ty Γ
  lam  : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  app  : Tm Γ (Π A B) → Tm (Γ ▹ A) B

  Π[]  : (Π A B) [ γ ]T ≡ Π (A [ γ ]T) (B [ γ ↑ A ]T)
  lam[] : TmΓ≡ Π[] (lam t [ γ ]t) ≡ lam (t [ γ ↑ A ]t)
  --lam[] : lam t [ γ ]t ≡[ Π[] ]≡ lam (t [ γ ↑ A ]t)  
  Πβ  : app (lam t) ≡ t  
  Πη  : lam (app t) ≡ t

  {- Universe of Small Types -}
  U    : Ty Γ
  El   : Tm Γ U → Ty Γ
  U[]  : U [ γ ]T ≡ U
  El[] : El t [ γ ]T ≡ El (TmΓ≡ U[] (t [ γ ]t))

{- Derivables -}

[id]t : TmΓ≡ [id]T (t [ id ]t) ≡ t
-- [id]t : t [ id ]t ≡[ [id]T ]≡ t
[id]t {Γ} {A} {t} =
  TmΓ≡ [id]T (t [ id ]t) ≡⟨ {!!} ⟩ -- ≡⟨ cong (TmΓ≡ [id]T) (sym π₂β) ⟩
  TmΓ≡ [id]T (TmΓ≡ (cong (A [_]T) π₁β) (π₂ (id , t [ id ]t))) ≡⟨ {!!} ⟩
  {!!} ≡⟨ {!!} ⟩ {!!}

{-
π₂β : TmΓ≡ (cong (A [_]T) π₁β) (π₂ (γ , t)) ≡ t

[id] : t [ id ] ≡ t
[id] {t = t} =
  t [ id ]                 ≡⟨ sym π₂β ⟩
  π₂ (id , t [ id ])       ≡⟨ cong (λ x → π₂ (x , t [ id ])) (sym idl) ⟩
  π₂ (id ∘ id , t [ id ])  ≡⟨ cong π₂ (sym ,∘) ⟩
  π₂ ((id , t) ∘ id)       ≡⟨ cong π₂ idr ⟩
  π₂ (id , t)              ≡⟨ π₂β ⟩
  t                        ∎
-}

{-
[∘]t  : TmΓ≡ [∘]T (t [ γ ∘ δ ]t) ≡ t [ γ ]t [ δ ]t
-- [∘]t  : t [ γ ∘ δ ]t ≡[ [∘]T ]≡ t [ γ ]t [ δ ]t
[∘]t {t = t} {γ = γ} {δ = δ} = {!!}
-}

wk : Tms (Γ ▹ A) Γ
wk = π₁ id

vz : Tm (Γ ▹ A) (A [ wk ]T)
vz = π₂ id

vs : Tm Γ A → Tm (Γ ▹ B) (A [ wk ]T)
vs t = t [ wk ]t

<_> : Tm Γ A → Tms Γ (Γ ▹ A)
< t > = id , TmΓ≡ (sym [id]T) t

_$_ : Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ < u > ]T)
t $ u = app t [ < u > ]t

{-
app[] : app (TmΓ≡ Π[] (t [ γ ]t)) ≡ app t [ γ ↑ A ]t
app[] {A = A} {t = t} {γ = γ} =
  app (TmΓ≡ Π[] (t [ γ ]t))               ≡⟨ cong (λ z → app (TmΓ≡ Π[] (z [ γ ]t))) (sym Πη) ⟩
  app (TmΓ≡ Π[] ((lam (app t) [ γ ]t)))   ≡⟨ cong app lam[] ⟩
  app (lam (app t [ γ ↑ A ]t))            ≡⟨ Πβ ⟩
  app t [ γ ↑ A ]t                        ∎
-}

β : lam t $ u ≡ (t [ < u > ]t)
β {u = u} = cong (_[ < u > ]t) Πβ

η : {A : Ty Γ} {B : Ty (Γ ▹ A)} {t : Tm Γ (Π A B)}
  → lam (TmΓ≡ Π[] (vs t) $ vz) ≡ {!t!}
  -- Tm Γ (Π A ((B [ wk ↑ A ]T) [ < vz > ]T))
η = {!!}
