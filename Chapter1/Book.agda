{-# OPTIONS --without-K --exact-split --safe --auto-inline --no-import-sorts #-}

module Chapter1.Book where

open import Lib.Universes public

---------------------------------------------------------------------------------

-- Section 1.4 Dependent function types

Π : {X : 𝒰 𝒾} (Y : X → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
Π {𝒾} {𝒿} {X} Y = (x : X) → Y x

-Π : (X : 𝒰 𝒾) (Y : X → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
-Π X Y = Π Y
infixr -1 -Π

syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {X : 𝒰 𝒾} → X → X
id a = a

𝑖𝑑 : (X : 𝒰 𝒾) → X → X
𝑖𝑑 X = id

swap : Π A ꞉ 𝒰 𝒾 , Π B ꞉ 𝒰 𝒿 , Π C ꞉ 𝒰 𝓀 , ((A → B → C) → (B → A → C))
swap A B C g b a = g a b

-- Helpers
domain : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 𝒾
domain {𝒾} {𝒿} {X} {Y} f = X

codomain : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 𝒿
codomain {𝒾} {𝒿} {X} {Y} f = Y

---------------------------------------------------------------------------------

-- Section 1.5 Product types

data 𝟙 : 𝒰₀ where
  ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝒰 𝒾) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

---------------------------------------------------------------------------------

-- Section 1.6 Dependent pairs types

record Σ {X : 𝒰 𝒾} (Y : X → 𝒰 𝒿) : 𝒰 (𝒾 ⊔ 𝒿) where
  constructor
    _,_
  field
    x : X
    y : Y x
infixr 50 _,_

-Σ : (X : 𝒰 𝒾) (Y : X → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
-Σ X Y = Σ Y
infixr -1 -Σ

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

_×_ : (X : 𝒰 𝒾) (Y : 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
X × Y = Σ x ꞉ X , Y
infixr 30 _×_

Σ-induction : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} {A : Σ Y → 𝒰 𝓀}
            → ((x : X) (y : Y x) → A (x , y))
            → ((x , y) : Σ Y) → A (x , y)

Σ-induction g (x , y) = g x y

pr₁ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

ac : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {R : A → B → 𝒰 𝓀}
   → (Π x ꞉ A , Σ y ꞉ B , R x y)
   → (Σ f ꞉ (A → B) , Π x ꞉ A , R x (f x))
ac g = ((λ x → pr₁ (g x)) , (λ x → pr₂ (g x)))

---------------------------------------------------------------------------------

-- Section 1.7 Coproduct types

data _⊎_ (X : 𝒰 𝒾) (Y : 𝒰 𝒿) : 𝒰 (𝒾 ⊔ 𝒿) where
 inl : X → X ⊎ Y
 inr : Y → X ⊎ Y
infixr 20 _⊎_

⊎-induction : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (A : X ⊎ Y → 𝒰 𝓀)
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X ⊎ Y) → A z

⊎-induction A f g (inl x) = f x
⊎-induction A f g (inr y) = g y

data 𝟘 : 𝒰₀ where

𝟘-induction : (A : 𝟘 → 𝒰 𝒾) → (x : 𝟘) → A x
𝟘-induction A ()

-- Simple helper
!𝟘 : (A : 𝒰 𝒾) → 𝟘 → A
!𝟘 A = 𝟘-induction (λ _ → A)

---------------------------------------------------------------------------------

-- Section 1.8 The type of booleans

𝟚 : 𝒰₀
𝟚 = 𝟙 ⊎ 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-induction : (A : 𝟚 → 𝒰 𝒾) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

-- 𝟚-induction : (A : 𝟚 → 𝒰 𝒾) → A (inl ⋆) → A (inr ⋆) → (x : 𝟚) → A x
-- 𝟚-induction A a1 a2 (inl ⋆) = a1
-- 𝟚-induction A a1 a2 (inr ⋆) = a2

---------------------------------------------------------------------------------

-- Section 1.9 The natural numbers

data ℕ : 𝒰₀ where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝒰 𝒾)
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n

ℕ-induction A a₀ f = h
  where
    h : (n : ℕ) → A n
    h 0        = a₀
    h (succ n) = f n (h n)

---------------------------------------------------------------------------------

-- Section 1.11 Propositions as types

¬ : 𝒰 𝒾 → 𝒰 𝒾
¬ X = X → 𝟘

-- helpers
¬¬ ¬¬¬ : 𝒰 𝒾 → 𝒰 𝒾
¬¬ X = ¬ (¬ X)
¬¬¬ X = ¬ (¬¬ X)

de-Morgan : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
          → (¬ A × ¬ B)
          → (¬ (A ⊎ B))
de-Morgan (f , g) (inl a) = f a
de-Morgan (f , g) (inr b) = g b

Π-of-× : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} {Q : A → 𝒰 𝒿} →
         (Π x ꞉ A , P x × Q x) →
         ((Π x ꞉ A , P x) × (Π x ꞉ A , Q x))
Π-of-× f = ((λ x → pr₁ (f x)) , (λ x → pr₂ (f x)))

---------------------------------------------------------------------------------

-- Section 1.12 Identity types

data Id (X : 𝒰 𝒾) : X → X → 𝒰 𝒾 where
  refl : (x : X) → Id X x x
infix   0 Id

_≡_ : {X : 𝒰 𝒾} → X → X → 𝒰 𝒾
x ≡ y = Id _ x y
infix   0 _≡_
{-# BUILTIN EQUALITY _≡_ #-}

-- Helper
_≢_ : {X : 𝒰 𝒾} → X → X → 𝒰 𝒾
x ≢ y = ¬(x ≡ y)

𝕁 : (X : 𝒰 𝒾) (A : (x y : X) → x ≡ y → 𝒰 𝒿)
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p

𝕁 X A f x x (refl x) = f x
