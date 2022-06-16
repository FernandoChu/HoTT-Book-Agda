{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Lib.Universes where

open import Agda.Primitive public
  renaming (
            Set to Universe
          ; lsuc to infix 1 _⁺
          ; Setω to 𝓤ω)

variable
  𝒾 𝒿 𝓀 : Level

𝒰 : (ℓ : Level) → Universe (ℓ ⁺)
𝒰 = λ x → Universe x
𝒰₀ = Universe lzero
𝒰₁ = Universe (lzero ⁺)
𝒰₂ = Universe (lzero ⁺ ⁺)
𝒰₃ = Universe (lzero ⁺ ⁺ ⁺)

universe-of : {ℓ : Level} (X : 𝒰 ℓ) → Level
universe-of {ℓ} X = ℓ

