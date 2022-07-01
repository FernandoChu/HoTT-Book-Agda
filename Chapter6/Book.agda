module Chapter6.Book where

open import Chapter6.HITs public

---------------------------------------------------------------------------------

-- 6.1 Introduction

module _ (circle  : CircleExists) where
 open module circle-data = Circle circle
 module _ (𝕊¹-rec-comp : {B : 𝒰 𝒾}
                       → (b : B)
                       → (l : b ≡ b)
                       → (ap (𝕊¹-rec b l) loop ≡ l))
          (𝕊¹-ind-comp : {P : 𝕊¹ → 𝒰 𝒾}
                       → (b : P base)
                       → (l : tr P loop b ≡ b)
                       → (apd (𝕊¹-ind b l) loop ≡ l))
          where

  test : 𝕊¹ → 𝟙
  test = 𝕊¹-rec ⋆ (refl ⋆)

  testcomp : test base ≡ ⋆
  testcomp = refl ⋆

module _ (interval : IntervalExists) where
 open module interval-data = Interval interval
 module _ (𝕀-rec-comp : {B : 𝒰 𝒾}
                      → (b₀ b₁ : B)
                      → (s : b₀ ≡ b₁)
                      → (ap (𝕀-rec b₀ b₁ s) seg ≡ s))
          (𝕀-ind-comp : {P : 𝕀 → 𝒰 𝒾}
                      → (b₀ : P 0ᵢ)
                      → (b₁ : P 1ᵢ)
                      → (s : tr P seg b₀ ≡ b₁)
                      → (apd (𝕀-ind b₀ b₁ s) seg ≡ s))
          where

  test𝕀 : 𝕀 → 𝕀
  test𝕀 = 𝕀-rec 0ᵢ 1ᵢ seg

  testcomp𝕀 : test𝕀 0ᵢ ≡ 0ᵢ
  testcomp𝕀 = refl 0ᵢ

  testcomp𝕀' : test𝕀 1ᵢ ≡ 1ᵢ
  testcomp𝕀' = refl 1ᵢ
