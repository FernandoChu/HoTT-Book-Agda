---
title: Chapter 5. Induction - Exercises
---

# Chapter 5. Induction - Exercises

```agda
module Chapter5.Exercises where

open import Chapter5.Book public

-- Exercise 5.4.
ind𝟚 : (E : 𝟚 → 𝒰 𝒾) → (E ₀ × E ₁) → ((b : 𝟚) → E b)
ind𝟚 E (e₀ , e₁) ₀ = e₀
ind𝟚 E (e₀ , e₁) ₁ = e₁

𝟚-ind-isequiv : (E : 𝟚 → 𝒰 𝒾)
              → isEquiv (ind𝟚 E)
𝟚-ind-isequiv E = invs⇒equivs (ind𝟚 E) (map⁻¹ , ε , η)
 where
  map⁻¹ = λ f → (f ₀ , f ₁)
  ε : (ind𝟚 E) ∘ map⁻¹ ∼ id
  ε f = funext (ind𝟚 (λ - → (ind𝟚 E ∘ map⁻¹) f - ≡ f -)
         (refl _ , refl _))
  η : map⁻¹ ∘ (ind𝟚 E) ∼ id
  η (e₀ , e₁) = refl _
```
