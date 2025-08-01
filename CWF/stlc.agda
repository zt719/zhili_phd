{-# OPTIONS --cubical --guardedness #-}

module STLC where

open import Cubical.Foundations.Prelude hiding (_,_)

{- Sorts -}
data UU : Set
data EL : UU → Set

data UU where
  con : UU
  ty  : UU
  tms : EL con → EL con → UU
  tm  : EL con → EL ty  → UU

Con : Set
Con = EL con

variable Γ Δ Θ : Con

Ty : Set
Ty = EL ty

variable A B C : Ty

Tms : Con → Con → Set
Tms Δ Γ = EL (tms Δ Γ)

variable γ δ θ : Tms Δ Γ

Tm : Con → Ty → Set
Tm Γ A = EL (tm Γ A)

variable t u : Tm Γ A

infixr 20 _⇒_
infixl 5 _▹_
infixl 5 _,_
infixr 9 _∘_

data EL where

  {- Rules for the category ℂ -}
  id   : Tms Γ Γ
  _∘_  : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
  idl  : id ∘ γ ≡ γ
  idr  : γ ∘ id ≡ γ
  ass  : (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
  
  {- Functor 𝐓 -}
  _[_] : Tm Γ A → Tms Δ Γ → Tm Δ A

  {- Rules for the terminal object -}
  ∙    : Con
  ε    : Tms Γ ∙
  ∙-η  : γ ≡ ε

  {- Rules for context comprehension -}
  _▹_  : Con → Ty → Con
  _,_  : Tms Δ Γ → Tm Δ A → Tms Δ (Γ ▹ A)
  π₁   : Tms Δ (Γ ▹ A) → Tms Δ Γ
  π₂   : Tms Δ (Γ ▹ A) → Tm Δ A
  π₁β  : π₁ (γ , t) ≡ γ
  π₂β  : π₂ (γ , t) ≡ t
  πη   : π₁ γ , π₂ γ ≡ γ
  ,∘   : (γ , t) ∘ δ ≡ γ ∘ δ , t [ δ ]

  _↑_ : Tms Δ Γ → (A : Ty) → Tms (Δ ▹ A) (Γ ▹ A)
  ↑≡  : γ ↑ A ≡ γ ∘ (π₁ id) , π₂ id

  {- Rules for function types -}
  _⇒_  : Ty → Ty → Ty
  lam    : Tm (Γ ▹ A) B → Tm Γ (A ⇒ B)
  app   : Tm Γ (A ⇒ B) → Tm (Γ ▹ A) B

  lam[] : (lam t) [ γ ] ≡ lam (t [ γ ↑ A ])
  ⇒β  : app (lam t) ≡ t  
  ⇒η  : lam (app t) ≡ t
 
  {- Rules for t universe of small types -}
  U : Ty
  El : Tm Γ U → Ty

{- Derivables. -}
[id] : t [ id ] ≡ t
[id] {t = t} =
  t [ id ]                 ≡⟨ sym π₂β ⟩
  π₂ (id , t [ id ])       ≡⟨ cong (λ x → π₂ (x , t [ id ])) (sym idl) ⟩
  π₂ (id ∘ id , t [ id ])  ≡⟨ cong π₂ (sym ,∘) ⟩
  π₂ ((id , t) ∘ id)       ≡⟨ cong π₂ idr ⟩
  π₂ (id , t)              ≡⟨ π₂β ⟩
  t                        ∎

[∘] : t [ γ ∘ δ ] ≡ t [ γ ] [ δ ]
[∘] {t = t} {γ = γ} {δ = δ} =
  t [ γ ∘ δ ]                        ≡⟨ sym π₂β ⟩
  π₂ (γ ∘ δ , t [ γ ∘ δ ])           ≡⟨ cong (λ x → π₂ (x , t [ γ ∘ δ ])) (sym idl) ⟩
  π₂ (id ∘ γ ∘ δ , t [ γ ∘ δ ])      ≡⟨ cong π₂ (sym ,∘) ⟩
  π₂ ((id , t) ∘ γ ∘ δ)              ≡⟨ cong π₂ (sym ass) ⟩
  π₂ (((id , t) ∘ γ) ∘ δ)            ≡⟨ cong (λ x → π₂ (x ∘ δ)) ,∘ ⟩
  π₂ ((id ∘ γ , t [ γ ]) ∘ δ)        ≡⟨ cong π₂ ,∘ ⟩
  π₂ ((id ∘ γ) ∘ δ , t [ γ ] [ δ ])  ≡⟨ π₂β ⟩
  t [ γ ] [ δ ]                      ∎

wk : Tms (Γ ▹ A) Γ
wk = π₁ id

vz : Tm (Γ ▹ A) A
vz = π₂ id

vs : Tm Γ A → Tm (Γ ▹ B) A
vs t = t [ wk ]

<_> : Tm Γ A → Tms Γ (Γ ▹ A)
< t > = id , t

_$_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
t $ u = app t [ < u > ]

β : lam t $ u ≡ t [ < u > ]
β {u = u} = cong _[ < u > ] ⇒β

vz-[] : vz [ γ , t ] ≡ t
vz-[] {γ = γ} {t = t} =
  π₂ id [ γ , t ]                         ≡⟨ sym π₂β ⟩
  π₂ (π₁ id ∘ (γ , t) , π₂ id [ γ , t ])  ≡⟨ cong π₂ (sym ,∘) ⟩
  π₂ ((π₁ id , π₂ id) ∘ (γ , t))          ≡⟨ cong (λ x → π₂ (x ∘ (γ , t))) πη ⟩
  π₂ (id ∘ (γ , t))                       ≡⟨ cong π₂ idl ⟩
  π₂ (γ , t)                              ≡⟨ π₂β ⟩
  t                                       ∎

vs-[] : vs t [ γ , u ] ≡ t [ γ ]
vs-[] {t = t} {γ = γ} {u = u} =
  t [ π₁ id ] [ γ , u ]                         ≡⟨ sym [∘] ⟩
  t [ π₁ id ∘ (γ , u) ]                         ≡⟨ cong (t [_]) (sym π₁β) ⟩
  t [ π₁ (π₁ id ∘ (γ , u) , π₂ id [ γ , u ]) ]  ≡⟨ cong (λ x → t [ π₁ x ]) (sym ,∘) ⟩
  t [ π₁ ((π₁ id , π₂ id) ∘ (γ , u)) ]          ≡⟨ cong (λ x → t [ π₁ (x ∘ (γ , u)) ]) πη ⟩
  t [ π₁ (id ∘ (γ , u)) ]                       ≡⟨ cong (λ x → t [ π₁ x ]) idl ⟩
  t [ π₁ (γ , u) ]                              ≡⟨ cong (t [_]) π₁β ⟩
  t [ γ ]                                       ∎

app[] : app (t [ γ ]) ≡ app t [ γ ↑ A ]
app[] {A = A} {t = t} {γ = γ} =
  app (t [ γ ])                ≡⟨ cong (λ x → app (x [ γ ])) (sym ⇒η) ⟩
  app (lam (app t) [ γ ])      ≡⟨ cong app lam[] ⟩
  app (lam (app t [ γ ↑ A ]))  ≡⟨ ⇒β ⟩
  app t [ γ ↑ A ]              ∎

{-
η : lam (vs t $ vz) ≡ t
η {t = t} =
  lam (app (t [ π₁ id ]) [ id , π₂ id ])     ≡⟨ {!!} ⟩
  lam (app t [ π₁ id ∘ id , π₂ id [ id ] ])  ≡⟨ {!!} ⟩
  lam (app t [ id ∘ π₁ id , π₂ id ])         ≡⟨ {!!} ⟩
  lam (app t [ id ↑ _ ])                     ≡⟨ cong (λ s → lam (app t [ s ])) {!!} ⟩
  lam (app t [ id ])                         ≡⟨ cong lam [id] ⟩
  lam (app t)                                ≡⟨ ⇒η ⟩
  t                                          ∎
-}
