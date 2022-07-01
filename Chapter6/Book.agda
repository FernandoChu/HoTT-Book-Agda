module Chapter6.Book where

open import Chapter6.HITs public

---------------------------------------------------------------------------------

-- 6.1 Introduction

module _
    (circle : CircleExists)
  where
  𝕊¹ = f𝕊¹ circle
  base = fbase circle
  loop = floop circle
  𝕊¹-rec = f𝕊¹-rec circle
  𝕊¹-ind = f𝕊¹-ind circle

  test : 𝕊¹ → 𝟙
  test = 𝕊¹-rec ⋆ (refl ⋆)

  testcomp : test base ≡ ⋆
  testcomp = refl ⋆

module _
    (interval : IntervalExists)
  where
  𝕀 = f𝕀 interval
  0ᵢ = f0ᵢ interval
  1ᵢ = f1ᵢ interval
  seg = fseg interval
  𝕀-rec = f𝕀-rec interval
  𝕀-ind = f𝕀-ind interval

  test𝕀 : 𝕀 → 𝕀
  test𝕀 = 𝕀-rec 0ᵢ 1ᵢ seg

  testcomp𝕀 : test𝕀 0ᵢ ≡ 0ᵢ
  testcomp𝕀 = refl 0ᵢ

  testcomp𝕀' : test𝕀 1ᵢ ≡ 1ᵢ
  testcomp𝕀' = refl 1ᵢ
