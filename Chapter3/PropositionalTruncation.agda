module Chapter3.PropositionalTruncation where

open import Chapter2.Exercises public

-- See https://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/

-- Propositional Truncations

module PropositionalTruncation where
  private
    data PT (A : 𝒰 𝒾) : 𝒰 𝒾 where
      forget : A → PT A

  ∥_∥ : {𝒾 : Level} → (A : 𝒰 𝒾) → 𝒰 𝒾
  ∥ A ∥ = PT A

  ∣_∣ : {𝒾 : Level} → {A : 𝒰 𝒾} → A → ∥ A ∥
  ∣ a ∣ = forget a

  ∥∥-rec : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
         → ((x y : B) → x ≡ y)
         → (g : A → B)
         → ∥ A ∥ → B
  ∥∥-rec A B p g (forget x) = g x

  postulate ∥∥-isProp : {X : 𝒰 𝒾} → (x y : ∥ X ∥) → x ≡ y

open PropositionalTruncation public
