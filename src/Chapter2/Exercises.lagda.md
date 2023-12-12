---
title: Chapter 2. Homotopy Type Theory - Exercises
---

# Chapter 2. Homotopy Type Theory - Exercises

```agda
module Chapter2.Exercises where

open import Chapter2.Book public

-- Exercise 2.1
≡-trans-alt₁ : {A : 𝒰 𝒾} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans-alt₁ (refl x) p = p

≡-trans-alt₂ : {A : 𝒰 𝒾} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans-alt₂ p (refl x) = p

≡-trans-equal₁ :
    {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → p ∙ q ≡ ≡-trans-alt₁ p q
≡-trans-equal₁ (refl _) (refl _) = refl _

≡-trans-equal₂ :
    {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → p ∙ q ≡ ≡-trans-alt₂ p q
≡-trans-equal₂ (refl _) (refl _) = refl _

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
