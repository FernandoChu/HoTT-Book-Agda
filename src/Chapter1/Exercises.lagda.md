---
title: Chapter 1. Type Theory - Exercises
---

# Chapter 1. Type Theory - Exercises

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

-- Exercise 1.2.
prj⇒rec-Σ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {C : 𝒰 𝓀}
          → ((x : A) (y : B x) → C)
          → Σ B → C
prj⇒rec-Σ g p = g (pr₁ p) (pr₂ p)

_ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {C : 𝒰 𝓀}
    → (g : (x : A) (y : B x) → C)
    → (p : Σ B) → (rec-Σ g p ≡ prj⇒rec-Σ g p)
_ = λ g p → refl _

-- As the following exercises need additional theorems about the identity type,
-- we will introduce some of them now in a private block. These will be later
-- redefined in Chapter 2.
private
  _⁻¹ : {A : 𝒰 𝒾} → {x y : A} → x ≡ y → y ≡ x
  (refl x)⁻¹ = refl x
  infix  40 _⁻¹

  _∙_ : {A : 𝒰 𝒾} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  (refl x) ∙ (refl x) = (refl x)
  infixl 30 _∙_

  begin_ : {A : 𝒰 𝒾} {x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y
  infix  1 begin_

  _≡⟨⟩_ : {A : 𝒰 𝒾} (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : {A : 𝒰 𝒾} (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = x≡y ∙ y≡z
  syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

  step-≡˘ : {A : 𝒰 𝒾} (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = (y≡x)⁻¹ ∙ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘

  _∎ : {A : 𝒰 𝒾} (x : A) → x ≡ x
  _∎ x = refl x
  infix  3 _∎

  ap : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) {x x' : A} → x ≡ x' → f x ≡ f x'
  ap f {x} {x'} (refl x) = refl (f x)

  tr : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿) {x y : A}
     → x ≡ y → P x → P y
  tr P (refl x) = id

-- Exercise 1.3.
uniq-Σ' : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} (z : Σ P)
        → z ≡ (pr₁ z , pr₂ z)
uniq-Σ' (x , y) = refl _

ind-Σ' : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {C : Σ B → 𝒰 𝓀}
       → ((x : A) (y : B x) → C (x , y))
       → ((x , y) : Σ B) → C (x , y)
ind-Σ' {C = C} g p =
  tr C ((uniq-Σ' p)⁻¹) (g (pr₁ p) (pr₂ p))

-- Exercise 1.4.
iter⇒rec-ℕ :
    (iter : (C : 𝒰 𝒾) → C → (C → C) → ℕ → C)
  → (C : 𝒰 𝒾)
  → C → (ℕ → C → C)
  → ℕ → C
iter⇒rec-ℕ iter C c₀ c'ₛ n =
  pr₁ (iter (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) n)

iter⇒rec-ℕ-comp-0 :
    (iter : (C : 𝒰 𝒾) → C → (C → C) → ℕ → C)
  → (iter-comp-0 : (C : 𝒰 𝒾) (c₀ : C) (cₛ : C → C) →  iter C c₀ cₛ 0 ≡ c₀)
  → (iter-comp-succ : (C : 𝒰 𝒾) (c₀ : C) (cₛ : C → C) (n : ℕ)
    → iter C c₀ cₛ (succ n) ≡ cₛ (iter C c₀ cₛ n))
  → (C : 𝒰 𝒾) (c₀ : C) (cₛ : ℕ → C → C)
  → iter⇒rec-ℕ iter C c₀ cₛ 0 ≡ c₀
iter⇒rec-ℕ-comp-0 iter iter-comp-0 iter-comp-succ C c₀ c'ₛ =
  ap pr₁ (iter-comp-0 (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)))

iter⇒rec-ℕ-comp-succ-helper :
    (iter : (C : 𝒰 𝒾) → C → (C → C) → ℕ → C)
  → (iter-comp-0 : (C : 𝒰 𝒾) (c₀ : C) (cₛ : C → C) →  iter C c₀ cₛ 0 ≡ c₀)
  → (iter-comp-succ : (C : 𝒰 𝒾) (c₀ : C) (cₛ : C → C) (n : ℕ)
    → iter C c₀ cₛ (succ n) ≡ cₛ (iter C c₀ cₛ n))
  → (C : 𝒰 𝒾) (c₀ : C) (c'ₛ : ℕ → C → C) (n : ℕ)
  → pr₂ (iter (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) n) ≡ n
iter⇒rec-ℕ-comp-succ-helper iter iter-comp-0 iter-comp-succ C c₀ c'ₛ zero =
  ap pr₂ (iter-comp-0 (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)))
iter⇒rec-ℕ-comp-succ-helper iter iter-comp-0 iter-comp-succ C c₀ c'ₛ (succ n) =
  begin
  pr₂ (iter (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) (succ n)) ≡⟨ i ⟩
  pr₂ ((λ (c , m) → (c'ₛ m c , succ m)) (itern))                        ≡⟨ ii ⟩
  pr₂ ((λ (c , m) → (c'ₛ m c , succ m)) (pr₁ itern , pr₂ itern))        ≡⟨⟩
  succ (pr₂ itern)                                                      ≡⟨ iii ⟩
  succ n                                                                ∎
  where
    i = ap pr₂
      (iter-comp-succ (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) n)
    itern = iter (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) n
    ii = ap (λ - → pr₂ ((λ (c , m) → (c'ₛ m c , succ m)) -))
      (uniq-Σ' (iter (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) n))
    iii = ap succ
      (iter⇒rec-ℕ-comp-succ-helper iter iter-comp-0 iter-comp-succ C c₀ c'ₛ n)

iter⇒rec-ℕ-comp-succ :
    (iter : (C : 𝒰 𝒾) → C → (C → C) → ℕ → C)
  → (iter-comp-0 : (C : 𝒰 𝒾) (c₀ : C) (cₛ : C → C) →  iter C c₀ cₛ 0 ≡ c₀)
  → (iter-comp-succ : (C : 𝒰 𝒾) (c₀ : C) (cₛ : C → C) (n : ℕ)
    → iter C c₀ cₛ (succ n) ≡ cₛ (iter C c₀ cₛ n))
  → (C : 𝒰 𝒾) (c₀ : C) (c'ₛ : ℕ → C → C) (n : ℕ)
  → iter⇒rec-ℕ iter C c₀ c'ₛ (succ n) ≡ c'ₛ n (iter⇒rec-ℕ iter C c₀ c'ₛ n)
iter⇒rec-ℕ-comp-succ iter iter-comp-0 iter-comp-succ C c₀ c'ₛ zero = begin
  iter⇒rec-ℕ iter C c₀ c'ₛ 1                                    ≡⟨ i ⟩
  pr₁ ((λ (c , m) → (c'ₛ m c , succ m))
    (iter (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) 0)) ≡⟨ ii ⟩
  pr₁ ((λ (c , m) → (c'ₛ m c , succ m)) (c₀ , 0))               ≡⟨⟩
  c'ₛ 0 c₀                                                      ≡˘⟨ iii ⟩
  c'ₛ zero (iter⇒rec-ℕ iter C c₀ c'ₛ zero)                      ∎
  where
    i = ap pr₁
      (iter-comp-succ (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) 0)
    ii = ap (λ - → pr₁ ((λ (c , m) → (c'ₛ m c , succ m)) -))
      (iter-comp-0 (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)))
    iii = ap (c'ₛ 0)
      (iter⇒rec-ℕ-comp-0 iter iter-comp-0 iter-comp-succ C c₀ c'ₛ)
iter⇒rec-ℕ-comp-succ iter iter-comp-0 iter-comp-succ C c₀ c'ₛ (succ n) = begin
  iter⇒rec-ℕ iter C c₀ c'ₛ (succ (succ n))                             ≡⟨ i ⟩
  pr₁ ((λ (c , m) → (c'ₛ m c , succ m)) iter-sn)                       ≡⟨ ii ⟩
  pr₁ ((λ (c , m) → (c'ₛ m c , succ m)) (pr₁ iter-sn , pr₂ iter-sn))   ≡⟨⟩
  c'ₛ (pr₂ iter-sn) (pr₁ iter-sn)                                      ≡⟨ iii ⟩
  c'ₛ (succ n) (iter⇒rec-ℕ iter C c₀ c'ₛ (succ n))                     ∎
  where
    iter-sn = iter (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) (succ n)
    i = ap pr₁
      (iter-comp-succ (C × ℕ) (c₀ , 0) (λ (c , m) → (c'ₛ m c , succ m)) (succ n))
    ii = ap (λ - → pr₁ ((λ (c , m) → (c'ₛ m c , succ m)) -)) (uniq-Σ' iter-sn)
    iii = ap (λ - → c'ₛ - (pr₁ iter-sn))
      (iter⇒rec-ℕ-comp-succ-helper
        iter iter-comp-0 iter-comp-succ C c₀ c'ₛ (succ n))
```
