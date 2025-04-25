{-# OPTIONS --cubical --type-in-type #-}

open import Cubical.Foundations.Prelude

record Cat : Set where
  field
    Obj : Set
    Hom : Obj → Obj → Set
    id : ∀ {X} → Hom X X
    _∘_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    idl : ∀ {X Y} (f : Hom X Y) → id ∘ f ≡ f
    idr : ∀ {X Y} (f : Hom X Y) → f ∘ id ≡ f
    {- ... -}

  FAM : Cat
  FAM .Obj = Σ[ I ∈ Set ] (I → Obj)
  FAM .Hom (I , F) (J , G) = Σ[ f ∈ (I → J) ] ((i : I) → Hom (F i) (G (f i)))
  FAM .id = (λ x → x) , (λ i → id)
  FAM ._∘_ (f , α) (g , β) = (λ x → f (g x)) , λ i → α (g i) ∘ β i
  FAM .idl (f , α) ci = f , λ i → idl (α i) ci
  FAM .idr (g , α) ci = g , λ i → idr (α i) ci

  FAM2 : Cat
  FAM2 .Obj = Σ[ I ∈ Set ] Σ[ J ∈ Set ] ((I → J → Obj))
  FAM2 .Hom (I , J , F) (I' , J' , G) =
    Σ[ f ∈ (I → I') ] Σ[ g ∈ (J → J') ] ((i : I) (j : J) → Hom (F i j) (G (f i) (g j)))
  FAM2 .id = (λ i → i) , (λ j → j) , λ i j → id
  FAM2 ._∘_ (f , g , α) (h , k , β) =
    (λ i → f (h i)) , (λ j → g (k j)) , λ i j → α (h i) (k j) ∘ β i j
  FAM2 .idl (f , g , α) ci = f , g , λ i j → idl (α i j) ci
  FAM2 .idr (f , g , α) ci = f , g , λ i j → idr (α i j) ci

  FAM⁻ : Cat
  FAM⁻ .Obj = Σ[ I ∈ Set ] (I → Obj)
  FAM⁻ .Hom (I , F) (J , G) = Σ[ f ∈ (I → J) ] ((i : I) → Hom (G (f i)) (F i))
  FAM⁻ .id = (λ i → i) , λ i → id
  FAM⁻ ._∘_ (f , α) (g ,  β) = (λ z → f (g z)) , λ i → β i ∘ α (g i)
  FAM⁻ .idl (f , α) ci = f , λ i → idr (α i) ci
  FAM⁻ .idr (f , α) ci = f , λ i → idl (α i) ci

open Cat
