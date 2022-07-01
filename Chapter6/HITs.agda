module Chapter6.HITs where

open import Chapter5.Exercises public

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

   f𝕊¹ : 𝒰₀
   f𝕊¹ = S

   fbase : f𝕊¹
   fbase = c base'

   floop : fbase ≡ fbase
   floop = ap c circle

   f𝕊¹-rec : {B : 𝒰 𝒾}
         → (b : B)
         → (l : b ≡ b)
         → f𝕊¹ -> B
   f𝕊¹-rec b _ point = b

   f𝕊¹-ind : {P : f𝕊¹ → 𝒰 𝒾}
          → (b : P fbase)
          → (l : tr P floop b ≡ b)
          → ((x : f𝕊¹) → P x)
   f𝕊¹-ind {𝒾} {P} b l (c x) =
     𝕊¹-ind-helper (λ x → P (c x)) b x

open Circle public

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
        → 𝕀' -> B
  𝕀-rec-helper b₀ b₁ _ Zero = b₀
  𝕀-rec-helper b₀ b₁ _ One = b₁

  𝕀-ind-helper : (P : 𝕀' → 𝒰 𝒾)
        → (b₀ : P 0ᵢ')
        → (b₁ : P 1ᵢ')
        → ((x : 𝕀') -> P x)
  𝕀-ind-helper P b₀ b₁ Zero = b₀
  𝕀-ind-helper P b₀ b₁ One = b₁

open Interval'

IntervalExists = 0ᵢ' ≡ 1ᵢ'

module _ (interval : IntervalExists) where
  module Interval where
    private
      data I : 𝒰₀ where
        i : 𝕀' → I

    f𝕀 : 𝒰₀
    f𝕀 = I

    f0ᵢ : f𝕀
    f0ᵢ = i 0ᵢ'

    f1ᵢ : f𝕀
    f1ᵢ = i 1ᵢ'

    fseg : f0ᵢ ≡ f1ᵢ
    fseg = ap i interval

    f𝕀-rec : {B : 𝒰 𝒾}
          → (b₀ b₁ : B)
          → (s : b₀ ≡ b₁)
          → f𝕀 -> B
    f𝕀-rec b₀ b₁ s (i x) = 𝕀-rec-helper b₀ b₁ s x

    f𝕀-ind : {P : f𝕀 → 𝒰 𝒾}
          → (b₀ : P f0ᵢ)
          → (b₁ : P f1ᵢ)
          → (s : tr P fseg b₀ ≡ b₁)
          → ((x : f𝕀) -> P x)
    f𝕀-ind {𝒾} {P} b₀ b₁ s (i x) =
      𝕀-ind-helper (λ x → P (i x)) b₀ b₁ x

open Interval public
