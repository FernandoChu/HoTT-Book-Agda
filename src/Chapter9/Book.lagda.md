---
title: Chapter 9. Category Theory
---

# Chapter 9. Category Theory

```
module Chapter9.Book where

open import Chapter8.Exercises public
```

## 9.1 Categories and precategories

```agda
-- Definition 9.1.1.
record Precategory (𝒾 𝒿 : Level) : 𝒰 ((𝒾 ⊔ 𝒿)⁺) where
  field
    Ob : 𝒰 𝒾
    Hom : Ob → Ob → 𝒰 𝒿
    Hom-set : (x y : Ob) → isSet (Hom x y)
    𝓲𝓭  : ∀ {x}     → Hom x x
    _⊚_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    idr : ∀ {x y} (f : Hom x y) → f ⊚ 𝓲𝓭 ≡ f
    idl : ∀ {x y} (f : Hom x y) → 𝓲𝓭 ⊚ f ≡ f
    assoc : ∀ {w x y z} (f : Hom y z) (g : Hom x y) (h : Hom w x)
          → f ⊚ (g ⊚ h) ≡ (f ⊚ g) ⊚ h

module _ {o h} (C : Precategory o h) where
  open Precategory C public
  variable
    a b c d : Ob
    f : Hom a b

  isIso : Hom a b → 𝒰 _
  isIso {a} {b} f = Σ g ꞉ (Hom b a) , ((f ⊚ g ≡ 𝓲𝓭) × (g ⊚ f ≡ 𝓲𝓭))

  _≅_ : Ob → Ob → 𝒰 _
  a ≅ b = Σ f ꞉ (Hom a b) , isIso f

  ≅-refl : (a : Ob) → a ≅ a
  ≅-refl a = 𝓲𝓭 , 𝓲𝓭 , (idl 𝓲𝓭 , idl 𝓲𝓭)

  idtoiso : a ≡ b → a ≅ b
  idtoiso (refl a) = ≅-refl a
```
