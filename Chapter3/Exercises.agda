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

-- Exercise 3.6
isProp→isDecidible-isProp : funext → (A : 𝒰 𝒾) → isProp A → isProp (A ⊎ (¬ A))
isProp→isDecidible-isProp fe A f (inl x) (inl y) = ap inl (f x y)
isProp→isDecidible-isProp fe A f (inl x) (inr c) = !𝟘 (inl x ≡ inr c) (c x)
isProp→isDecidible-isProp fe A f (inr c) (inl x) = !𝟘 (inr c ≡ inl x) (c x)
isProp→isDecidible-isProp fe A f (inr c) (inr d) = ap inr p
  where
    p : c ≡ d
    p = pr₁ (pr₁ (fe c d)) (λ x → !𝟘 (c x ≡ d x) (c x))

-- Exercise 3.7
isProp→isDecidible-isProp' : (A : 𝒰 𝒾) → (B : 𝒰 𝒿)
                          → isProp A → isProp B → ¬ (A × B)
                          → isProp (A ⊎ B)
isProp→isDecidible-isProp' A B f g c (inl a) (inl a') =
  ap inl (f a a')
isProp→isDecidible-isProp' A B f g c (inl a) (inr b) =
  !𝟘 (inl a ≡ inr b) (c (a , b))
isProp→isDecidible-isProp' A B f g c (inr b) (inl a) =
  !𝟘 (inr b ≡ inl a) (c (a , b))
isProp→isDecidible-isProp' A B f g c (inr b) (inr b') =
  ap inr (g b b')
