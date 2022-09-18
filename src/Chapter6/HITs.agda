module Chapter6.HITs where

open import Chapter5.Exercises public

-- See https://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/

---------------------------------------------------------------------------------

-- Circle

module Circle where
  private
    data S : 𝒰₀ where
      point : S

  𝕊¹ : 𝒰₀
  𝕊¹ = S

  base : S
  base = point

  postulate loop : base ≡ base

  𝕊¹-ind : (P : 𝕊¹ → 𝒰 𝒾)
         → (b : P base)
         → (l : tr P loop b ≡ b)
         → ((x : 𝕊¹) → P x)
  𝕊¹-ind P b l point = b

  postulate 𝕊¹-ind-comp : (P : 𝕊¹ → 𝒰 𝒾)
                        → (b : P base)
                        → (l : tr P loop b ≡ b)
                        → (apd (𝕊¹-ind P b l) loop ≡ l)

open Circle public

---------------------------------------------------------------------------------

-- Interval

module Interval where
  private
    data I : 𝒰₀ where
      Zero : I
      One  : I

  𝕀 : 𝒰₀
  𝕀 = I

  0ᵢ : 𝕀
  0ᵢ = Zero

  1ᵢ : 𝕀
  1ᵢ = One

  postulate seg : 0ᵢ ≡ 1ᵢ

  𝕀-rec : (B : 𝒰 𝒾)
        → (b₀ b₁ : B)
        → (s : b₀ ≡ b₁)
        → 𝕀 → B
  𝕀-rec B b₀ b₁ s Zero = b₀
  𝕀-rec B b₀ b₁ s One = b₁

  𝕀-ind : (P : 𝕀 → 𝒰 𝒾)
        → (b₀ : P 0ᵢ)
        → (b₁ : P 1ᵢ)
        → (s : tr P seg b₀ ≡ b₁)
        → ((x : 𝕀) → P x)
  𝕀-ind P b₀ b₁ s Zero = b₀
  𝕀-ind P b₀ b₁ s One = b₁

  postulate 𝕀-rec-comp : (B : 𝒰 𝒾)
                       → (b₀ b₁ : B)
                       → (s : b₀ ≡ b₁)
                       → (ap (𝕀-rec B b₀ b₁ s) seg ≡ s)
  postulate 𝕀-ind-comp : (P : 𝕀 → 𝒰 𝒾)
                       → (b₀ : P 0ᵢ)
                       → (b₁ : P 1ᵢ)
                       → (s : tr P seg b₀ ≡ b₁)
                       → (apd (𝕀-ind P b₀ b₁ s) seg ≡ s)

open Interval public

---------------------------------------------------------------------------------

-- Suspensions

module Suspension where
  private
    data Sus (A : 𝒰 𝒾) : 𝒰 𝒾 where
      Zero : Sus A
      One : Sus A

  𝝨 : (A : 𝒰 𝒾) → 𝒰 𝒾
  𝝨 A = Sus A

  N : (A : 𝒰 𝒾) → (Sus A)
  N A = Zero

  S : (A : 𝒰 𝒾) → (Sus A)
  S A = One

  postulate merid : (A : 𝒰 𝒾) → A → N A ≡ S A

  𝝨-rec : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
        → (n s : B)
        → (m : A → (n ≡ s))
        → 𝝨 A → B
  𝝨-rec A B n s m Zero = n
  𝝨-rec A B n s m One = s

  𝝨-ind : (A : 𝒰 𝒾) (P : 𝝨 A → 𝒰 𝒿)
        → (n : P (N A)) → (s : P (S A))
        → (m : (a : A) → tr P (merid A a) n ≡ s)
        → ((x : 𝝨 A) → P x)
  𝝨-ind A P n s m Zero = n
  𝝨-ind A P n s m One = s

  postulate 𝝨-rec-comp : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
              → (n s : B)
              → (m : A → (n ≡ s))
              → ((a : A) → ap (𝝨-rec A B n s m) (merid A a) ≡ (m a))

  postulate 𝝨-ind-comp : (A : 𝒰 𝒾) (P : 𝝨 A → 𝒰 𝒿)
              → (n : P (N A)) → (s : P (S A))
              → (m : (a : A) → tr P (merid A a) n ≡ s)
              → ((a : A) → (apd (𝝨-ind A P n s m) (merid A a) ≡ m a))

open Suspension public

