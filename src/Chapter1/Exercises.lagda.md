```agda
module Chapter1.Exercises where

open import Chapter1.Book public

-- Exercise 1.1
_∘_ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {Z : Y → 𝒰 𝓀}
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)
infixl 70 _∘_
```
