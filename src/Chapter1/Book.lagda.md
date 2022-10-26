---
title: Chapter 1. Type Theory
---

# Chapter 1. Type Theory

We begin with importing the Agda primitives and renaming them to match the notation of book.

```agda
module Chapter1.Book where

open import Agda.Primitive public
  renaming ( Set to Universe
           ; lsuc to infix 1 _⁺
           ; Setω to 𝓤ω)

variable
  𝒾 𝒿 𝓀 : Level

𝒰 : (ℓ : Level) → Universe (ℓ ⁺)
𝒰 ℓ = Universe ℓ

𝒰₀ = Universe lzero

_⁺⁺ : (ℓ : Level) → Level
ℓ ⁺⁺ = (ℓ ⁺) ⁺

universe-of : {ℓ : Level} (A : 𝒰 ℓ) → Level
universe-of {ℓ} A = ℓ
```

## Section 1.3 Dependent function types

```agda
-- Workaround to have cumulativity
data Raised (𝒿 : Level) (A : 𝒰 𝒾) : 𝒰 (𝒾 ⊔ 𝒿) where
  raise : A → Raised 𝒿 A
```

## Section 1.4 Dependent function types

```agda
Π : {A : 𝒰 𝒾} (B : A → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
Π {𝒾} {𝒿} {A} B = (x : A) → B x

-Π : (A : 𝒰 𝒾) (B : A → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
-Π A B = Π B
infixr -1 -Π

syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {A : 𝒰 𝒾} → A → A
id a = a

𝑖𝑑 : (A : 𝒰 𝒾) → A → A
𝑖𝑑 A = id

swap : Π A ꞉ 𝒰 𝒾 , Π B ꞉ 𝒰 𝒿 , Π C ꞉ 𝒰 𝓀 , ((A → B → C) → (B → A → C))
swap A B C g b a = g a b

-- Helpers
domain : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → B) → 𝒰 𝒾
domain {𝒾} {𝒿} {A} {B} f = A

codomain : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → B) → 𝒰 𝒿
codomain {𝒾} {𝒿} {A} {B} f = B
```

## Section 1.5 Product types

```agda
data 𝟙 : 𝒰₀ where
  ⋆ : 𝟙

ind-𝟙 : (A : 𝟙 → 𝒰 𝒾) → A ⋆ → (x : 𝟙) → A x
ind-𝟙 A a ⋆ = a
```

## Section 1.6 Dependent pairs types

```agda
record Σ {A : 𝒰 𝒾} (B : A → 𝒰 𝒿) : 𝒰 (𝒾 ⊔ 𝒿) where
  constructor
    _,_
  field
    x : A
    y : B x
infixr 50 _,_

-Σ : (A : 𝒰 𝒾) (B : A → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
-Σ A B = Σ B
infixr -1 -Σ

syntax -Σ A (λ x → y) = Σ x ꞉ A , y

_×_ : (A : 𝒰 𝒾) (B : 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
A × B = Σ x ꞉ A , B
infixr 30 _×_

ind-Σ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {C : Σ B → 𝒰 𝓀}
      → ((x : A) (y : B x) → C (x , y))
      → ((x , y) : Σ B) → C (x , y)
ind-Σ g (x , y) = g x y

pr₁ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} → Σ B → A
pr₁ (x , y) = x

pr₂ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} → (z : Σ B) → B (pr₁ z)
pr₂ (x , y) = y

ac : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {R : A → B → 𝒰 𝓀}
   → (Π x ꞉ A , Σ y ꞉ B , R x y)
   → (Σ f ꞉ (A → B) , Π x ꞉ A , R x (f x))
ac g = ((λ x → pr₁ (g x)) , (λ x → pr₂ (g x)))
```

## Section 1.7 Coproduct types

```agda
data _⊎_ (A : 𝒰 𝒾) (B : 𝒰 𝒿) : 𝒰 (𝒾 ⊔ 𝒿) where
 inl : A → A ⊎ B
 inr : B → A ⊎ B
infixr 20 _⊎_

⊎-rec : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (C : 𝒰 𝓀)
      → ((x : A) → C)
      → ((y : B) → C)
      → (A ⊎ B → C)
⊎-rec C f g (inl x) = f x
⊎-rec C f g (inr y) = g y

⊎-ind : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (C : A ⊎ B → 𝒰 𝓀)
      → ((x : A) → C (inl x))
      → ((y : B) → C (inr y))
      → (z : A ⊎ B) → C z
⊎-ind C f g (inl x) = f x
⊎-ind C f g (inr y) = g y

data 𝟘 : 𝒰₀ where

ind-𝟘 : (A : 𝟘 → 𝒰 𝒾) → (x : 𝟘) → A x
ind-𝟘 A ()

-- Simple helper
!𝟘 : (A : 𝒰 𝒾) → 𝟘 → A
!𝟘 A = ind-𝟘 (λ _ → A)
```

## Section 1.8 The type of booleans

```agda
𝟚 : 𝒰₀
𝟚 = 𝟙 ⊎ 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-rec : (C : 𝒰 𝒾) → C → C → 𝟚 → C
𝟚-rec C c₀ c₁ ₀ = c₀
𝟚-rec C c₀ c₁ ₁ = c₁

ind-𝟚 : (A : 𝟚 → 𝒰 𝒾) → A ₀ → A ₁ → (n : 𝟚) → A n
ind-𝟚 A a₀ a₁ ₀ = a₀
ind-𝟚 A a₀ a₁ ₁ = a₁
```

## Section 1.9 The natural numbers

```agda
data ℕ : 𝒰₀ where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

ind-ℕ : (A : ℕ → 𝒰 𝒾)
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ind-ℕ A a₀ f = h
  where
    h : (n : ℕ) → A n
    h 0        = a₀
    h (succ n) = f n (h n)
```

## Section 1.11 Propositions as types

```agda
¬ : 𝒰 𝒾 → 𝒰 𝒾
¬ A = A → 𝟘

-- Helpers
¬¬ ¬¬¬ : 𝒰 𝒾 → 𝒰 𝒾
¬¬ A = ¬ (¬ A)
¬¬¬ A = ¬ (¬¬ A)

de-Morgan : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
          → (¬ A × ¬ B)
          → (¬ (A ⊎ B))
de-Morgan (f , g) (inl a) = f a
de-Morgan (f , g) (inr b) = g b

Π-of-× : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} {Q : A → 𝒰 𝒿} →
         (Π x ꞉ A , P x × Q x) →
         ((Π x ꞉ A , P x) × (Π x ꞉ A , Q x))
Π-of-× f = ((λ x → pr₁ (f x)) , (λ x → pr₂ (f x)))
```

## Section 1.12 Identity types

```agda
data Id (A : 𝒰 𝒾) : A → A → 𝒰 𝒾 where
  refl : (x : A) → Id A x x
infix   0 Id

_≡_ : {A : 𝒰 𝒾} → A → A → 𝒰 𝒾
x ≡ y = Id _ x y
infix   0 _≡_
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

-- Helper
_≢_ : {A : 𝒰 𝒾} → A → A → 𝒰 𝒾
x ≢ y = ¬(x ≡ y)

ind-≡ : (A : 𝒰 𝒾) (D : (x y : A) → x ≡ y → 𝒰 𝒿)
  → ((x : A) → D x x (refl x))
  → (x y : A) (p : x ≡ y) → D x y p
ind-≡ A D d x x (refl x) = d x
```
