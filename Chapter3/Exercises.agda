{-# OPTIONS --without-K --exact-split --safe --auto-inline --no-import-sorts #-}

module Chapter3.Exercises where

open import Chapter3.Book public

-- Exercise 3.4
prop-if-endo-are-contr : funext → (A : 𝒰 𝒾) → isProp A → isContr (A → A)
prop-if-endo-are-contr fe A h = (id , p)
  where
    p : (g : A → A) → id ≡ g
    p g = (pr₁ (pr₁ (fe id g))) (λ x → h x (g x))

contr-endo-implies-prop : (A : 𝒰 𝒾) → isContr (A → A) → isProp A
contr-endo-implies-prop A h x y = happly f g (A→A-isProp f g) x
  where
    A→A-isProp : isProp (A → A)
    A→A-isProp = pr₂ (contr-are-pointed-props (A → A) h)
    f : A → A
    f - = x
    g : A → A
    g - = y
