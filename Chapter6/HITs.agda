module Chapter6.HITs where

open import Chapter5.Exercises public

-- See https://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/

---------------------------------------------------------------------------------

-- Circle

private module Circle' where
  private
    data S : 𝒰₀ where
      point : S

  𝕊¹' : 𝒰₀
  𝕊¹' = S

  base' : S
  base' = point

  𝕊¹-ind-helper : (P : S → 𝒰 𝒾)
                → (b : P base')
                → ((x : S) → P x)
  𝕊¹-ind-helper P b point = b

open Circle'

CircleExists = base' ≡ base'

module _ (circle : CircleExists) where
  module Circle where
   private
    data S : 𝒰₀ where
     c : 𝕊¹' → S

   𝕊¹ : 𝒰₀
   𝕊¹ = S

   base : 𝕊¹
   base = c base'

   loop : base ≡ base
   loop = ap c circle

   𝕊¹-ind : (P : 𝕊¹ → 𝒰 𝒾)
          → (b : P base)
          → (l : tr P loop b ≡ b)
          → ((x : 𝕊¹) → P x)
   𝕊¹-ind P b l (c x) =
     𝕊¹-ind-helper (λ x → P (c x)) b x

---------------------------------------------------------------------------------

-- Interval

private module Interval' where
  private
    data I : 𝒰₀ where
      Zero : I
      One  : I

  𝕀' : 𝒰₀
  𝕀' = I

  0ᵢ' : 𝕀'
  0ᵢ' = Zero

  1ᵢ' : 𝕀'
  1ᵢ' = One

  𝕀-rec-helper : {B : 𝒰 𝒾}
        → (b₀ b₁ : B)
        → (s : b₀ ≡ b₁)
        → 𝕀' → B
  𝕀-rec-helper b₀ b₁ _ Zero = b₀
  𝕀-rec-helper b₀ b₁ _ One = b₁

  𝕀-ind-helper : (P : 𝕀' → 𝒰 𝒾)
        → (b₀ : P 0ᵢ')
        → (b₁ : P 1ᵢ')
        → ((x : 𝕀') → P x)
  𝕀-ind-helper P b₀ b₁ Zero = b₀
  𝕀-ind-helper P b₀ b₁ One = b₁

open Interval'

IntervalExists = 0ᵢ' ≡ 1ᵢ'

module _ (interval : IntervalExists) where
  module Interval where
    private
      data I : 𝒰₀ where
        i : 𝕀' → I

    𝕀 : 𝒰₀
    𝕀 = I

    0ᵢ : 𝕀
    0ᵢ = i 0ᵢ'

    1ᵢ : 𝕀
    1ᵢ = i 1ᵢ'

    seg : 0ᵢ ≡ 1ᵢ
    seg = ap i interval

    𝕀-rec : (B : 𝒰 𝒾)
          → (b₀ b₁ : B)
          → (s : b₀ ≡ b₁)
          → 𝕀 → B
    𝕀-rec B b₀ b₁ s (i x) = 𝕀-rec-helper b₀ b₁ s x

    𝕀-ind : (P : 𝕀 → 𝒰 𝒾)
          → (b₀ : P 0ᵢ)
          → (b₁ : P 1ᵢ)
          → (s : tr P seg b₀ ≡ b₁)
          → ((x : 𝕀) → P x)
    𝕀-ind P b₀ b₁ s (i x) =
      𝕀-ind-helper (λ x → P (i x)) b₀ b₁ x
