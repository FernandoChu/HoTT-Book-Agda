---
title: Chapter 1. Type Theory - Exercises
---

# Chapter 1. Type Theory - Exercises

```agda
module Chapter1.Exercises where

open import Chapter1.Book public

-- Exercise 1.1
_∘_ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {Z : Y → 𝒰 𝓀}
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)
infixl 70 _∘_

-- Exercise 1.2.
prj⇒rec-Σ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {C : 𝒰 𝓀}
          → ((x : A) (y : B x) → C)
          → Σ B → C
prj⇒rec-Σ g p = g (pr₁ p) (pr₂ p)

_ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {C : 𝒰 𝓀}
    → (g : (x : A) (y : B x) → C)
    → (p : Σ B) → (rec-Σ g p ≡ prj⇒rec-Σ g p)
_ = λ g p → refl _

-- Exercise 1.3.
uniq-Σ' : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} (z : Σ P)
        → z ≡ (pr₁ z , pr₂ z)
uniq-Σ' (x , y) = refl _

ind-Σ' : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {C : Σ B → 𝒰 𝓀}
       → ((x : A) (y : B x) → C (x , y))
       → ((x , y) : Σ B) → C (x , y)
ind-Σ' {C = C} g p =
  tr' C (uniq-Σ' p) (g (pr₁ p) (pr₂ p))
  where
    tr' : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿) {x y : A}
       → x ≡ y → P y → P x
    tr' P (refl x) = id
```
