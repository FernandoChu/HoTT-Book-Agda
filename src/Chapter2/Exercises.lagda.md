---
title: Chapter 2. Homotopy Type Theory - Exercises
---

# Chapter 2. Homotopy Type Theory - Exercises

```agda
module Chapter2.Exercises where

open import Chapter2.Book public

-- Exercise 2.1
_∙₂_ : {A : 𝒰 𝒾} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙₂_ (refl x) p = p

_∙₃_ : {A : 𝒰 𝒾} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙₃_ p (refl x) = p

∙₁≡∙₂ :
    {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → p ∙ q ≡ p ∙₂ q
∙₁≡∙₂ (refl _) (refl _) = refl _

∙₂≡∙₃ :
    {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → p ∙₂ q ≡ p ∙₃ q
∙₂≡∙₃ (refl _) (refl _) = refl _

∙₁≡∙₃ :
    {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → p ∙ q ≡ p ∙₃ q
∙₁≡∙₃ (refl _) (refl _) = refl _

-- Exercise 2.2
Exercise-2-2 :
    {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → (∙₁≡∙₂ p q) ∙ (∙₂≡∙₃ p q) ≡ (∙₁≡∙₃ p q)
Exercise-2-2 (refl _) (refl _) = refl _

-- Exercise 2.3
_∙₄_ : {A : 𝒰 𝒾} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙₄_ {x = x} p q = tr (λ - → x ≡ -) q p

∙₁≡∙₄ :
    {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → p ∙ q ≡ p ∙₄ q
∙₁≡∙₄ (refl _) (refl _) = refl _

-- Exercise 2.10
Σ-assoc : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} (C : (Σ x ꞉ A , B x) → 𝒰 𝓀)
        → (Σ x ꞉ A , (Σ y ꞉ B x , C (x , y))) ≃ (Σ p ꞉ (Σ x ꞉ A , B x) , C p)
Σ-assoc C = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = λ (x , y , c) → ((x , y) , c)
  map⁻¹ = λ ((x , y) , c) → (x , y , c)
  ε = refl
  η = refl

-- Exercise 2.17 iii)
-- Σ-≃-fst is on Chapter6, as it is easier to prove it with more theorems
Σ-≃-snd : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} {Q : A → 𝒰 𝓀}
        → ((x : A) → P x ≃ Q x)
        → -Σ A P ≃ -Σ A Q
Σ-≃-snd f = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = λ (x , px) → (x , ≃-→ (f x) px)
  map⁻¹ = λ (x , px) → (x , ≃-← (f x) px)
  ε = λ (x , px) → pair⁼(refl x , ≃-ε (f x) px)
  η = λ (x , px) → pair⁼(refl x , ≃-η (f x) px)
```
