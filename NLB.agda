{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Function.Base

N : Set → Set
N X = Unit ⊎ X

N₁ : {X Y : Set}
  → (X → Y)
  → N X → N Y
N₁ f (inl tt) = inl tt
N₁ f (inr x) = inr (f x)

N-id : {X : Set}
  → N₁ {X} id ≡ id
N-id i (inl tt) = inl tt
N-id i (inr x) = inr x

N-∘ : {X Y Z : Set}
  → (f : Y → Z) (g : X → Y)
  → N₁ (f ∘ g) ≡ N₁ f ∘ N₁ g
N-∘ f g i (inl tt) = inl tt
N-∘ f g i (inr x) = inr (f (g x))


L : (Set → Set) → Set → Set
L F X = Unit ⊎ F X

L₁ : {F G : Set → Set}
  → ((X : Set) → F X → G X)
  → (X : Set) → L F X → L G X
L₁ α X (inl tt) = inl tt
L₁ α X (inr x) = inr (α X x)

L-id : {X : Set} {F : Set → Set}
  → L₁ {F} (λ _ → id) X ≡ id
L-id i (inl tt) = inl tt
L-id i (inr x) = inr x

L-∘ : {F G H : Set → Set}
  → (α : (X : Set) → G X → H X)
  → (β : (X : Set) → F X → G X)
  → (X : Set) → L₁ (λ X → α X ∘ β X) X ≡  L₁ α X ∘ L₁ β X
L-∘ α β X i (inl tt) = inl tt
L-∘ α β X i (inr x) = inr (α X (β X x))

B : (Set → Set) → Set → Set
B F X = X × F (F X)

B₁ : {F G : Set → Set}
  → {G₁ : {X Y : Set} → (X → Y) → G X → G Y}
  → (α : (X : Set) → F X → G X)
  → (X : Set) → B F X → B G X
B₁ {F} {G} {G₁} α X (x , ffx) = x , G₁ (α X) ((α (F X)) ffx)

B-id : {F : Set → Set}
  → {F₁ : {X Y : Set} → (X → Y) → F X → F Y}
  → {F-id : {X : Set} → F₁ {X} id ≡ id}
  → (X : Set) → B₁ {F} {F} {F₁} (λ _ → id) X ≡ id
B-id {F-id = F-id} X i (x , ffx) = x , F-id i ffx

B-∘ : {F G H : Set → Set}
  → {G₁ : {X Y : Set} → (X → Y) → G X → G Y}
  → {H₁ : {X Y : Set} → (X → Y) → H X → H Y}
  → {H-∘ : {X Y Z : Set} (f : Y → Z) (g : X → Y)
         → H₁ (f ∘ g) ≡ H₁ f ∘ H₁ g}
  → (α : (X : Set) → G X → H X)
  → {α-nat : {X Y : Set} (f : X → Y)
            → H₁ f ∘ α X ≡ α Y ∘ G₁ f}
  → (β : (X : Set) → F X → G X)
  → (X : Set) → B₁ {_} {_} {H₁} (λ X → α X ∘ β X) X
    ≡ B₁ {_} {_} {H₁} α X ∘ B₁ {_} {_} {G₁} β X
B-∘ {F} {G} {H} {G₁} {H₁} {H-∘} α {α-nat} β X i (x , ffx)
  = x ,
  ( H₁ (α X ∘ β X) ((α (F X) ∘ β (F X)) ffx)
  ≡⟨ (λ j → H-∘ (α X) (β X) j (α (F X) (β (F X) ffx))) ⟩
    H₁ (α X) (H₁ (β X) (α (F X) (β (F X) ffx)))
  ≡⟨ (λ j → H₁ (α X) (α-nat (β X) j (β (F X) ffx))) ⟩
    H₁ (α X) (α (G X) (G₁ (β X) (β (F X) ffx))) 
  ∎ ) i


U : (Set → Set) → Set
U F = F Unit

U₁ : {F G : Set → Set}
  → (α : (X : Set) → F X → G X)
  → U F → U G
U₁ α cf = α Unit cf

U-id : {F : Set → Set}
  → U₁ {F} (λ _ → id) ≡ id
U-id = refl

U-∘ : {F G H : Set → Set}
  → (α : (X : Set) → G X → H X)
  → (β : (X : Set) → F X → G X)
  → U₁ (λ X → α X ∘ β X) ≡ (U₁ α) ∘ U₁ β
U-∘ α β = refl


C : Set → Set → Set
C X _ = X

C₁ : {X Y : Set}
  → (X → Y)
  → (Z : Set) → C X Z → C Y Z
C₁ f _ = f

C-id : {X : Set}
  → C₁ {X} id ≡ λ _ → id
C-id = refl

C-∘ : {X Y Z : Set}
  → (f : Y → Z) (g : X → Y)
  → C₁ (f ∘ g) ≡ λ Z → C₁ f Z ∘ C₁ g Z
C-∘ f g = refl
