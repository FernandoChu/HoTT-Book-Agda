---
title: Wedges sum of circles
---

# Wedges sum of circles

It is an [open problem](https://ncatlab.org/nlab/show/loop+space+of+a+wedge+of+circles)
if the loop space of a wedge sum of circles is the free group on the index.

```agda
module AdittionalTopics.WedgesOfCircles where

open import Chapter11.Exercises public
```

## Definition of the wedge sum of circles

```agda
module _ (A : 𝒰 𝒾) (A-isSet : isSet A) where
  postulate
    WA : 𝒰₀
    baseWA : WA
    loopWA : A → baseWA ≡ baseWA
    WA-rec : (B : 𝒰 𝒿)
          → (b : B)
          → (m : A → (b ≡ b))
          → WA → B
    WA-rec-comp-base : (B : 𝒰 𝒿)
          → (b : B)
          → (m : A → (b ≡ b))
          → WA-rec B b m baseWA ≡ b
    {-# REWRITE WA-rec-comp-base #-}
    WA-rec-comp : (B : 𝒰 𝒿)
          → (b : B)
          → (m : A → (b ≡ b))
          → (a : A) → ap (WA-rec B b m) (loopWA a) ≡ m a
    WA-ind : (P : WA → 𝒰 𝒿)
          → (b : P baseWA)
          → (m : (a : A) → (tr P (loopWA a) b ≡ b))
          → (x : WA) → P x
    WA-ind-comp-base : (P : WA → 𝒰 𝒿)
          → (b : P baseWA)
          → (m : (a : A) → (tr P (loopWA a) b ≡ b))
          → WA-ind P b m baseWA ≡ b
    {-# REWRITE WA-ind-comp-base #-}
    WA-ind-comp : (P : WA → 𝒰 𝒿)
          → (b : P baseWA)
          → (m : (a : A) → (tr P (loopWA a) b ≡ b))
          → (a : A) → apd (WA-ind P b m) (loopWA a) ≡ m a
```
