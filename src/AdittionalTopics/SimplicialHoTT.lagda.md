---
title: Simplicial HoTT
---

# Simplicial HoTT

The 2-simplex can be postulated internally in HoTT.

```agda
module AdittionalTopics.SimplicialHoTT where

open import Chapter11.Exercises public
```

## Definition of the 2-Simplex

```agda
postulate
  Δ² : 𝒰₀
  isSet-Δ² : isSet Δ²
  Δ²₀ Δ²₁ : Δ²
  _Δ²-≤_ : Δ² → Δ² → Prop𝒰 lzero
  Δ²₀≤Δ²₀ : pr₁ (Δ²₀ Δ²-≤ Δ²₁)
  Δ²₀≤Δ²₁ : pr₁ (Δ²₀ Δ²-≤ Δ²₁)
  Δ²₁≤Δ²₀ : ¬ (pr₁ (Δ²₀ Δ²-≤ Δ²₁))
  Δ²₁≤Δ²₁ : pr₁ (Δ²₀ Δ²-≤ Δ²₁)

ΔHom : {𝒾 : Level} (A : 𝒰 𝒾) (a b : A) → 𝒰 𝒾
ΔHom A a b = Σ f ꞉ (Δ² → A) , (f Δ²₀ ≡ a) × (f Δ²₁ ≡ b)  
```
