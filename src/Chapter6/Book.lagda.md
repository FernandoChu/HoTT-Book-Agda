---
title: Chapter 6. Higher Inductive Types
---

# Chapter 6. Higher Inductive Types

```agda
module Chapter6.Book where

open import Chapter5.Exercises public
```

## 6.1 Introduction

Workaround: Since HIT's are not available in agda, I'm implementing
them in another module. I need two nested modules to claim they exist
and have the appropriate computing rules (for the paths).
They compute as they should in the points.

```agda
postulate
  𝕊¹ : 𝒰₀
  base : 𝕊¹
  loop : base ≡ base
  𝕊¹-ind : (P : 𝕊¹ → 𝒰 𝒾)
         → (b : P base)
         → (l : tr P loop b ≡ b)
         → ((x : 𝕊¹) → P x)
  𝕊¹-ind-comp-base : (P : 𝕊¹ → 𝒰 𝒾)
                   → (b : P base)
                   → (l : tr P loop b ≡ b)
                   → 𝕊¹-ind P b l base ≡ b
  {-# REWRITE 𝕊¹-ind-comp-base #-}
  𝕊¹-ind-comp : (P : 𝕊¹ → 𝒰 𝒾)
              → (b : P base)
              → (l : tr P loop b ≡ b)
              → (apd (𝕊¹-ind P b l) loop ≡ l)

postulate
  𝕀 : 𝒰₀
  0ᵢ : 𝕀
  1ᵢ : 𝕀
  seg : 0ᵢ ≡ 1ᵢ
  𝕀-rec : (B : 𝒰 𝒾)
        → (b₀ b₁ : B)
        → (s : b₀ ≡ b₁)
        → 𝕀 → B
  𝕀-rec-comp-0ᵢ : (B : 𝒰 𝒾)
                → (b₀ b₁ : B)
                → (s : b₀ ≡ b₁)
                → 𝕀-rec B b₀ b₁ s 0ᵢ ≡ b₀
  𝕀-rec-comp-1ᵢ : (B : 𝒰 𝒾)
                → (b₀ b₁ : B)
                → (s : b₀ ≡ b₁)
                → 𝕀-rec B b₀ b₁ s 1ᵢ ≡ b₁
  {-# REWRITE 𝕀-rec-comp-0ᵢ 𝕀-rec-comp-1ᵢ #-}
  𝕀-rec-comp : (B : 𝒰 𝒾)
             → (b₀ b₁ : B)
             → (s : b₀ ≡ b₁)
             → (ap (𝕀-rec B b₀ b₁ s) seg ≡ s)
  𝕀-ind : (P : 𝕀 → 𝒰 𝒾)
        → (b₀ : P 0ᵢ)
        → (b₁ : P 1ᵢ)
        → (s : tr P seg b₀ ≡ b₁)
        → ((x : 𝕀) → P x)
  𝕀-ind-comp-0ᵢ : (P : 𝕀 → 𝒰 𝒾)
                → (b₀ : P 0ᵢ)
                → (b₁ : P 1ᵢ)
                → (s : tr P seg b₀ ≡ b₁)
                → 𝕀-ind P b₀ b₁ s 0ᵢ ≡ b₀
  𝕀-ind-comp : (P : 𝕀 → 𝒰 𝒾)
             → (b₀ : P 0ᵢ)
             → (b₁ : P 1ᵢ)
             → (s : tr P seg b₀ ≡ b₁)
             → 𝕀-ind P b₀ b₁ s 1ᵢ ≡ b₁
```

## 6.2 Induction principles and dependent paths

```agda
-- Lemma 6.2.5.
𝕊¹-rec : (A : 𝒰 𝒾)
       → (a : A)
       → (p : a ≡ a)
       → 𝕊¹ → A
𝕊¹-rec A a p = 𝕊¹-ind (λ - → A) a (trconst A loop a ∙ p)

𝕊¹-rec-comp : (A : 𝒰 𝒾)
            → (a : A)
            → (p : a ≡ a)
            → (ap (𝕊¹-rec A a p) loop ≡ p)
𝕊¹-rec-comp A a p = ∙-left-cancel (trconst A loop a) (ii ⁻¹ ∙ i)
 where
  f = 𝕊¹-rec A a p
  i : apd f loop ≡ trconst A loop a ∙ p
  i = 𝕊¹-ind-comp (λ - → A) a (trconst A loop a ∙ p)
  ii : apd f loop ≡ trconst A loop a ∙ ap f loop
  ii = apd-trconst A f loop

-- Lemma 6.2.6.
𝕊¹-ind-uniq : {A : 𝒰 𝒾}
            → (f g : 𝕊¹ → A)
            → (p : f base ≡ g base)
            → (tr (λ x → x ≡ x) p (ap f loop) ≡ ap g loop)
            → ((x : 𝕊¹) → f x ≡ g x)
𝕊¹-ind-uniq {𝒾} {A} f g p q = 𝕊¹-ind (λ x → f x ≡ g x) p iii
 where
  i : tr (λ z → f z ≡ g z) loop p ≡ (ap f loop)⁻¹ ∙ p ∙ ap g loop
  i = tr-fx≡gx f g loop p
  ii : ap f loop ∙ p ≡ p ∙ ap g loop
  ii = ≃-→ (tr-x≡x-≃ p (ap f loop) (ap g loop)) q
  iii = begin
   tr (λ z → f z ≡ g z) loop p     ≡⟨ i ⟩
   (ap f loop)⁻¹ ∙ p ∙ ap g loop   ≡⟨ ∙-assoc ((ap f loop)⁻¹) ⟩
   (ap f loop)⁻¹ ∙ (p ∙ ap g loop) ≡˘⟨ ap ((ap f loop)⁻¹ ∙_) ii ⟩
   (ap f loop)⁻¹ ∙ (ap f loop ∙ p) ≡˘⟨ ∙-assoc ((ap f loop)⁻¹) ⟩
   (ap f loop)⁻¹ ∙ ap f loop ∙ p   ≡⟨ ap (_∙ p) (⁻¹-left∙ (ap f loop)) ⟩
   refl _ ∙ p                      ≡⟨ refl-left ⟩
   p                               ∎

-- Lemma 6.2.9.
𝕊¹→-≃ : {A : 𝒰 𝒾}
      → (𝕊¹ → A) ≃ (Σ x ꞉ A , x ≡ x)
𝕊¹→-≃ {𝒾} {A} = φ , invs⇒equivs φ (φ⁻¹ , ε , η)
  where
    φ = λ f → (f base , ap f loop)
    φ⁻¹ = λ (b , l) → 𝕊¹-rec A b l
    ε = λ (b , l) → pair⁼(refl b , 𝕊¹-rec-comp A b l)
    η = λ f → funext (𝕊¹-ind-uniq _ _ (refl _) (𝕊¹-rec-comp A _ _))
```

## 6.3 The interval

```agda
𝕀-isContr : isContr 𝕀
𝕀-isContr = (1ᵢ , λ x → (contr x)⁻¹)
 where
  contr : (x : 𝕀) → (x ≡ 1ᵢ)
  contr = 𝕀-ind (λ x → x ≡ 1ᵢ) seg (refl 1ᵢ) tr-eq
   where
    tr-eq : tr (λ x → x ≡ 1ᵢ) seg seg ≡ refl 1ᵢ
    tr-eq = (tr-Hom─c 1ᵢ seg seg) ∙ (⁻¹-left∙ seg)
```

## 6.4 Circles and spheres

```agda
-- Lemma 6.4.1.
loop≢refl : loop ≢ refl base
loop≢refl eq = ¬-isSet-𝒰₀ (A-is-set 𝒰₀)
 where
  A-is-set : (A : 𝒰 𝒾) → isSet A
  A-is-set A {x} {y} p (refl x) = p≡refl
   where
    f : 𝕊¹ → A
    f = 𝕊¹-rec A x p
    p≡refl : p ≡ refl x
    p≡refl = (𝕊¹-rec-comp A x p)⁻¹ ∙ (ap (λ - → ap f -) eq)

-- Lemma 6.4.4.
ap² : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {x y : A} {p q : x ≡ y}
      (f : A → B) (r : p ≡ q)
    → ap f p ≡ ap f q
ap² f (refl p) = refl _

-- Lemma 6.4.5.
tr² : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿) {x y : A}
      {p q : x ≡ y} (r : p ≡ q) (u : P x)
    → tr P p u ≡ tr P q u
tr² P (refl p) u = refl _

apd² : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} {x y : A} {p q : x ≡ y}
       (f : (x : A) → P x) (r : p ≡ q)
     → apd f p ≡ (tr² P r (f x) ∙ apd f q)
apd² f (refl p) = (refl-left)⁻¹
```

## 6.5 Suspensions

```agda
postulate
  𝝨 : (A : 𝒰 𝒾) → 𝒰 𝒾
  N : (A : 𝒰 𝒾) → 𝝨 A
  S : (A : 𝒰 𝒾) → 𝝨 A
  merid : (A : 𝒰 𝒾) → A → N A ≡ S A
  𝝨-rec : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
        → (n s : B)
        → (m : A → (n ≡ s))
        → 𝝨 A → B
  𝝨-rec-comp-N : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
              → (n s : B)
              → (m : A → (n ≡ s))
              → 𝝨-rec A B n s m (N A) ≡ n
  {-# REWRITE 𝝨-rec-comp-N #-}
  𝝨-rec-comp-S : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
              → (n s : B)
              → (m : A → (n ≡ s))
              → 𝝨-rec A B n s m (S A) ≡ s
  {-# REWRITE 𝝨-rec-comp-S #-}
  𝝨-rec-comp : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
              → (n s : B)
              → (m : A → (n ≡ s))
              → ((a : A) → ap (𝝨-rec A B n s m) (merid A a) ≡ (m a))
  𝝨-ind : (A : 𝒰 𝒾) (P : 𝝨 A → 𝒰 𝒿)
        → (n : P (N A)) → (s : P (S A))
        → (m : (a : A) → tr P (merid A a) n ≡ s)
        → ((x : 𝝨 A) → P x)
  𝝨-ind-comp-N : (A : 𝒰 𝒾) (P : 𝝨 A → 𝒰 𝒿)
              → (n : P (N A)) → (s : P (S A))
              → (m : (a : A) → tr P (merid A a) n ≡ s)
              → 𝝨-ind A P n s m (N A) ≡ n
  {-# REWRITE 𝝨-ind-comp-N #-}
  𝝨-ind-comp-S : (A : 𝒰 𝒾) (P : 𝝨 A → 𝒰 𝒿)
              → (n : P (N A)) → (s : P (S A))
              → (m : (a : A) → tr P (merid A a) n ≡ s)
              → 𝝨-ind A P n s m (S A) ≡ s
  {-# REWRITE 𝝨-ind-comp-S #-}
  𝝨-ind-comp : (A : 𝒰 𝒾) (P : 𝝨 A → 𝒰 𝒿)
              → (n : P (N A)) → (s : P (S A))
              → (m : (a : A) → tr P (merid A a) n ≡ s)
              → ((a : A) → (apd (𝝨-ind A P n s m) (merid A a) ≡ m a))

-- Lemma 6.5.1.
𝝨𝟚≃𝕊¹ : 𝝨 𝟚 ≃ 𝕊¹
𝝨𝟚≃𝕊¹ = f , invs⇒equivs f (g , ε , η)
 where
  f = 𝝨-rec 𝟚 𝕊¹ base base (𝟚-rec (base ≡ base) loop (refl base))
  g = 𝕊¹-rec (𝝨 𝟚) (N 𝟚) (merid 𝟚 ₀ ∙ (merid 𝟚 ₁)⁻¹)
  η : g ∘ f ∼ id
  η = 𝝨-ind 𝟚 (λ - → g (f -) ≡ -) (refl _) (merid 𝟚 ₁) lemma
   where
    lemma : (y : 𝟚)
          → tr (λ - → g (f -) ≡ -)
                (merid 𝟚 y) (refl _) ≡ merid 𝟚 ₁
    lemma y = begin
      tr (λ - → g (f -) ≡ -)
          (merid 𝟚 y) (refl _)               ≡⟨ I ⟩
      (ap (g ∘ f) (merid 𝟚 y))⁻¹ ∙ refl _
          ∙ ap id (merid 𝟚 y)                ≡⟨ II ⟩
      (ap (g ∘ f) (merid 𝟚 y))⁻¹ ∙ refl _
          ∙ merid 𝟚 y                        ≡⟨ III ⟩
      (ap (g ∘ f) (merid 𝟚 y))⁻¹ ∙ merid 𝟚 y ≡⟨ IV y ⟩
      merid 𝟚 ₁ ∎
     where
      I = tr-fx≡gx (g ∘ f) id (merid 𝟚 y) (refl _)
      II = ap ((ap (g ∘ f) (merid 𝟚 y))⁻¹ ∙ refl _ ∙_) (ap-id (merid 𝟚 y))
      III = ap (_∙ merid 𝟚 y) refl-right
      IV : (y : 𝟚) → (ap (g ∘ f) (merid 𝟚 y))⁻¹ ∙ merid 𝟚 y ≡ merid 𝟚 ₁
      IV ₀ = (ap (g ∘ f) (merid 𝟚 ₀))⁻¹ ∙ merid 𝟚 ₀   ≡⟨ i ⟩
        (ap g ∘ ap f) (merid 𝟚 ₀) ⁻¹ ∙ merid 𝟚 ₀      ≡⟨ ii ⟩
        (ap g loop)⁻¹ ∙ merid 𝟚 ₀                     ≡⟨ iii ⟩
        (merid 𝟚 ₀ ∙ (merid 𝟚 ₁)⁻¹)⁻¹ ∙ merid 𝟚 ₀     ≡⟨ iv ⟩
        ((merid 𝟚 ₁)⁻¹)⁻¹ ∙ (merid 𝟚 ₀)⁻¹ ∙ merid 𝟚 ₀ ≡⟨ v ⟩
        merid 𝟚 ₁ ∙ (merid 𝟚 ₀)⁻¹ ∙ merid 𝟚 ₀         ≡⟨ vi ⟩
        merid 𝟚 ₁ ∙ ((merid 𝟚 ₀)⁻¹ ∙ merid 𝟚 ₀)       ≡⟨ vii ⟩
        merid 𝟚 ₁ ∙ (refl (S 𝟚))                      ≡⟨ viii ⟩
        merid 𝟚 ₁ ∎
       where
        i    = ap (λ - → (-)⁻¹ ∙ merid 𝟚 ₀) (ap-∘ f g (merid 𝟚 ₀))
        ii   = ap (λ - → (ap g -)⁻¹ ∙ merid 𝟚 ₀)
                   (𝝨-rec-comp 𝟚 𝕊¹ base base
                    (𝟚-rec (base ≡ base) loop (refl base)) ₀)
        iii  = ap (λ - → (-)⁻¹ ∙ merid 𝟚 ₀)
               (𝕊¹-rec-comp (𝝨 𝟚) (N 𝟚) (merid 𝟚 ₀ ∙ (merid 𝟚 ₁)⁻¹))
        iv   = ap (_∙ merid 𝟚 ₀) (⁻¹-∙ (merid 𝟚 ₀))
        v    = ap (λ - → - ∙ (merid 𝟚 ₀)⁻¹ ∙ merid 𝟚 ₀)
                (⁻¹-involutive (merid 𝟚 ₁))
        vi   = ∙-assoc (merid 𝟚 ₁)
        vii  = ap (merid 𝟚 ₁ ∙_) (⁻¹-left∙ (merid 𝟚 ₀))
        viii = refl-right
      IV ₁ = begin
        (ap (g ∘ f) (merid 𝟚 ₁))⁻¹ ∙ merid 𝟚 ₁   ≡⟨ i ⟩
        (ap g ∘ ap f) (merid 𝟚 ₁) ⁻¹ ∙ merid 𝟚 ₁ ≡⟨ ii ⟩
        (ap g (refl base))⁻¹ ∙ merid 𝟚 ₁         ≡⟨ iii ⟩
        (refl (N 𝟚))⁻¹ ∙ merid 𝟚 ₁               ≡⟨ iv ⟩
        (refl (N 𝟚)) ∙ merid 𝟚 ₁                 ≡⟨ v ⟩
        merid 𝟚 ₁ ∎
       where
        i   = ap (λ - → (-)⁻¹ ∙ merid 𝟚 ₁) (ap-∘ f g (merid 𝟚 ₁))
        ii  = ap (λ - → (ap g -)⁻¹ ∙ merid 𝟚 ₁)
                 (𝝨-rec-comp 𝟚 𝕊¹ base base
                 (𝟚-rec (base ≡ base) loop (refl base)) ₁)
        iii = ap (λ - → (-)⁻¹ ∙ merid 𝟚 ₁) (refl (refl (N 𝟚)))
        iv  = ap (_∙ merid 𝟚 ₁) (refl (refl (N 𝟚)))
        v   = refl-left

  ε : f ∘ g ∼ id
  ε = 𝕊¹-ind (λ - → f (g -) ≡ -) (refl base) lemma
   where
    lemma : tr (λ - → f (g -) ≡ -) loop (refl base) ≡ refl base
    lemma = begin
      tr (λ - → f (g -) ≡ -) loop (refl base)            ≡⟨ I ⟩
      (ap (f ∘ g) loop)⁻¹ ∙ refl base ∙ ap id loop       ≡⟨ II ⟩
      (ap (f ∘ g) loop)⁻¹ ∙ refl base ∙ loop             ≡⟨ III ⟩
      (ap (f ∘ g) loop)⁻¹ ∙ loop                         ≡⟨ IV ⟩
      (ap f (ap g loop))⁻¹ ∙ loop                        ≡⟨ V ⟩
      (ap f (merid 𝟚 ₀ ∙ (merid 𝟚 ₁)⁻¹))⁻¹ ∙ loop        ≡⟨ VI ⟩
      (ap f (merid 𝟚 ₀) ∙ ap f ((merid 𝟚 ₁)⁻¹))⁻¹ ∙ loop ≡⟨ VII ⟩
      (loop ∙ ap f ((merid 𝟚 ₁)⁻¹))⁻¹ ∙ loop             ≡⟨ VIII ⟩
      (loop ∙ (ap f (merid 𝟚 ₁))⁻¹)⁻¹ ∙ loop             ≡⟨ IX ⟩
      (loop ∙ refl base)⁻¹ ∙ loop                        ≡⟨ X ⟩
      (loop)⁻¹ ∙ loop                                    ≡⟨ XI ⟩
      refl base ∎
     where
      I    = tr-fx≡gx (f ∘ g) id loop (refl _)
      II   = ap ((ap (f ∘ g) loop)⁻¹ ∙ refl _ ∙_) (ap-id loop)
      III  = ap (_∙ loop) refl-right
      IV   = ap (λ - → (-)⁻¹ ∙ loop) (ap-∘ g f loop)
      V    = ap (λ - → (ap f -)⁻¹ ∙ loop)
                 (𝕊¹-rec-comp (𝝨 𝟚) (N 𝟚) (merid 𝟚 ₀ ∙ (merid 𝟚 ₁)⁻¹))
      VI   = ap (λ - → (-)⁻¹ ∙ loop) (ap-∙ f (merid 𝟚 ₀) ((merid 𝟚 ₁)⁻¹))
      VII  = ap (λ - → (- ∙ ap f ((merid 𝟚 ₁)⁻¹))⁻¹ ∙ loop)
                 (𝝨-rec-comp 𝟚 𝕊¹ base base
                  (𝟚-rec (base ≡ base) loop (refl base)) ₀)
      VIII = ap (λ - → (loop ∙ -)⁻¹ ∙ loop) (ap-⁻¹ f (merid 𝟚 ₁))⁻¹
      IX   = ap (λ - → (loop ∙ (-)⁻¹)⁻¹ ∙ loop)
                 (𝝨-rec-comp 𝟚 𝕊¹ base base
                  (𝟚-rec (base ≡ base) loop (refl base)) ₁)
      X    = ap (λ - → (-)⁻¹ ∙ loop) refl-right
      XI   = ⁻¹-left∙ loop

-- Definition 6.5.2.
𝕊ⁿ : (n : ℕ) → 𝒰₀
𝕊ⁿ zero = 𝟚
𝕊ⁿ (succ n) = 𝝨 (𝕊ⁿ n)

Map* : ((A , a₀) : 𝒰∙ 𝒾) → ((B , b₀) : 𝒰∙ 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
Map* (A , a₀) (B , b₀) = Σ f ꞉ (A → B) , f a₀ ≡ b₀

_₊ : (A : 𝒰 𝒾) → 𝒰∙ 𝒾
A ₊ = (A ⊎ 𝟙) , inr ⋆

-- Lemma 6.5.3.
Map*₊≃ : (A : 𝒰 𝒾) → ((B , b₀) : 𝒰∙ 𝒿)
      → Map* (A ₊) (B , b₀) ≃ (A → B)
Map*₊≃ A (B , b₀) = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = λ (f , eq) → f ∘ inl
  map⁻¹ = λ g → ⊎-rec B g (λ - → b₀) , refl b₀
  ε : map ∘ map⁻¹ ∼ id
  ε = λ g → refl g
  η : map⁻¹ ∘ map ∼ id
  η (f , eq) = pair⁼(f'≡f , eqtr)
   where
    f' = λ (x : A ⊎ 𝟙) → pr₁ (map⁻¹ (f ∘ inl)) x

    f'∼f : f' ∼ f
    f'∼f = ⊎-ind (λ x → pr₁ (map⁻¹ (f ∘ inl)) x ≡ f x) (λ - → refl _) helper
     where
      helper : (y : 𝟙) → b₀ ≡ f (inr y)
      helper ⋆ = eq ⁻¹

    f'≡f : f' ≡ f
    f'≡f = funext f'∼f

    eqtr : tr (λ f → (f (inr ⋆)) ≡ b₀) f'≡f (refl b₀) ≡ eq
    eqtr = begin
      tr (λ f → (f (inr ⋆)) ≡ b₀) f'≡f (refl b₀)   ≡⟨ i ⟩
      (happly f'≡f (inr ⋆))⁻¹ ∙ refl b₀ ∙
        ap (λ - → b₀) f'≡f                         ≡⟨ ii ⟩
      (happly f'≡f (inr ⋆))⁻¹ ∙ ap (λ - → b₀) f'≡f ≡⟨ iii ⟩
      (happly f'≡f (inr ⋆))⁻¹ ∙ (refl b₀)          ≡⟨ iv ⟩
      (happly f'≡f (inr ⋆))⁻¹                      ≡⟨ v ⟩
      (f'∼f (inr ⋆))⁻¹                             ≡⟨⟩
      (eq ⁻¹)⁻¹                                    ≡⟨ vi ⟩
      eq                                           ∎
     where
      i   = tr-fx≡gx (λ - → - (inr ⋆)) (λ - → b₀) f'≡f (refl b₀)
      ii  = ap (_∙ ap (λ - → b₀) f'≡f) refl-right
      iii = ap ((ap (λ - → - (inr ⋆)) f'≡f)⁻¹ ∙_) (ap-const f'≡f b₀)
      iv  = refl-right
      v   = ap (λ - → (- (inr ⋆))⁻¹) (≡-Π-comp f'∼f)
      vi  = ⁻¹-involutive eq

-- Unnumbered corollary
Map*𝟚→-≃ : ((B , b₀) : 𝒰∙ 𝒿)
         → Map* (𝟚 , ₁) (B , b₀) ≃ B
Map*𝟚→-≃ (B , b₀) = Map*₊≃ 𝟙 (B , b₀) ≃∙ 𝟙→B≃B
 where
  𝟙→B≃B : (𝟙 → B) ≃ B
  𝟙→B≃B = (λ f → f ⋆) , invs⇒equivs (λ f → f ⋆)
    ((λ {b ⋆ → b}) , refl , λ f → funext λ {⋆ → refl _})

-- Needed Lemma for Lemma 6.5.4. (it's exercise 6.11)
𝝨→-≃ : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
     → (𝝨 A → B) ≃ (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ)))
𝝨→-≃ A B = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map : (𝝨 A → B) → (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ)))
  map f = (f (N A) , f (S A) , λ x → ap f (merid A x))
  map⁻¹ : (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ))) → (𝝨 A → B)
  map⁻¹ (bₙ , bₛ , g) = 𝝨-rec A B bₙ bₛ g
  ε : (map  ∘ map⁻¹) ∼ id
  ε (bₙ , bₛ , g) =
    pair⁼(refl bₙ ,
      pair⁼(refl bₛ ,
        funext (λ x → 𝝨-rec-comp A B bₙ bₛ g x)))
  η : (map⁻¹  ∘ map) ∼ id
  η f = funext (λ x →
    𝝨-ind A (λ - → (map⁻¹ ∘ map) f - ≡ id f -)
      (refl _) (refl _) (λ a → (begin
        tr (λ - → map⁻¹ (map f) - ≡ f -) (merid A a)
           (refl (map⁻¹ (map f) (N A)))              ≡⟨ i a ⟩
        ap (map⁻¹ (map f)) (merid A a) ⁻¹
          ∙ refl (map⁻¹ (map f) (N A))
          ∙ ap f (merid A a)                         ≡⟨ ii a ⟩
        ap (map⁻¹ (map f)) (merid A a) ⁻¹
          ∙ ap f (merid A a)                         ≡⟨ iii a ⟩
        ap f (merid A a) ⁻¹
          ∙ ap f (merid A a)                         ≡⟨ iv a ⟩
        refl (map⁻¹ (map f) (S A)) ∎)) x)
   where
    i = λ a → tr-fx≡gx (map⁻¹ (map f)) f (merid A a) (refl _)
    ii = λ a → ap (_∙ ap f (merid A a)) refl-right
    iii = λ a → ap (λ - → - ⁻¹ ∙ ap f (merid A a))
      (𝝨-rec-comp A B (f (N A)) (f (S A)) (λ x → ap f (merid A x)) a)
    iv = λ a → ⁻¹-left∙ (ap f (merid A a))

-- Additional lemma
Σ-≃-fst : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (A≃B : A ≃ B) (P : A → 𝒰 𝓀)
     → (Σ x ꞉ A , P x) ≃ (Σ y ꞉ B , P (≃-← A≃B y))
Σ-≃-fst {A = A} {B} A≃B P = map , invs⇒equivs map (map⁻¹ , ε' , η')
 where
  f = ≃-→ A≃B
  g = ≃-← A≃B
  hae' : isHae' f
  hae' = (isHae⇒isHae' f ∘ isQinv⇒isHae f ∘ equivs⇒invs f) (pr₂ A≃B)
  η = pr₁ (pr₂ hae')
  ε = pr₁ (pr₂ (pr₂ hae'))
  ν = pr₂ (pr₂ (pr₂ hae'))

  map : (Σ x ꞉ A , P x) → (Σ y ꞉ B , P (g y))
  map (x , px) = (f x , tr P ((η x)⁻¹) px)
  map⁻¹ : (Σ y ꞉ B , P (g y)) → (Σ x ꞉ A , P x)
  map⁻¹ (y , py) = (g y , py)

  ε' : (map  ∘ map⁻¹) ∼ id
  ε' (y , py) = pair⁼(ε y , (begin
    tr (P ∘ (≃-← A≃B)) (ε y)
       (tr P ((η (≃-← A≃B y))⁻¹) py) ≡⟨ i ⟩
    tr P (ap (≃-← A≃B) (ε y))
       (tr P ((η (≃-← A≃B y))⁻¹) py) ≡⟨ ii ⟩
    tr P ((η (≃-← A≃B y))⁻¹
      ∙ ap (≃-← A≃B) (ε y)) py       ≡⟨ iii ⟩
    tr P ((ap (≃-← A≃B) (ε y))⁻¹
      ∙ ap (≃-← A≃B) (ε y)) py       ≡⟨ iv ⟩
    py ∎))
   where
    i = happly (tr-ap' P (≃-← A≃B) (ε y)) (tr P ((η (≃-← A≃B y))⁻¹) py)
    ii = happly (tr-∘ P ((≃-η A≃B (≃-← A≃B y))⁻¹) (ap (≃-← A≃B) (ε y))) py
    iii = ap (λ - → tr P (- ⁻¹ ∙ ap (≃-← A≃B) (ε y)) py) ((ν y)⁻¹)
    iv = ap (λ - → tr P - py) (⁻¹-left∙ (ap (≃-← A≃B) (ε y)))

  η' : (map⁻¹  ∘ map) ∼ id
  η' (x , px) = pair⁼(η x , (begin
    tr P (η x) (tr P ((η x)⁻¹) px) ≡⟨ i ⟩
    tr P ((η x)⁻¹ ∙ (η x)) px      ≡⟨ ii ⟩
    px ∎))
   where
    i = happly (tr-∘ P ((η x)⁻¹) (η x)) px
    ii = ap (λ - → tr P - px) (⁻¹-left∙ (η x))

-- Lemma 6.5.4.
Map*𝝨≃ : ((A , a₀) : 𝒰∙ 𝒾) ((B , b₀) : 𝒰∙ 𝒿)
       → Map* (𝝨 A , N A) (B , b₀) ≃ Map* (A , a₀) (Ω (B , b₀))
Map*𝝨≃ (A , a₀) (B , b₀) =
  eqv1 ≃∙ eqv2 ≃∙ eqv3 ≃∙ eqv4 ≃∙ eqv5 ≃∙ eqv6 ≃∙ eqv7
 where
  eqv1 : (Σ f ꞉ (𝝨 A → B) , f (N A) ≡ b₀) ≃
           (Σ f ꞉ (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ))) , (pr₁ f ≡ b₀))
  eqv1 = Σ-≃-fst (𝝨→-≃ A B) (λ f → f (N A) ≡ b₀)
  eqv2 : (Σ f ꞉ (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ))) , (pr₁ f ≡ b₀)) ≃
           (Σ bₙ ꞉ B , Σ bₛ ꞉ B , ((A → (bₙ ≡ bₛ)) × (bₙ ≡ b₀)))
  eqv2 = eqv21 ≃∙ (Σ-≃-snd eqv22)
   where
    eqv21 : (Σ f ꞉ (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ))) , (pr₁ f ≡ b₀)) ≃
              (Σ bₙ ꞉ B , Σ f ꞉ (Σ bₛ ꞉ B , (A → bₙ ≡ bₛ)) , bₙ ≡ b₀)
    eqv21 = ≃-sym (Σ-assoc (λ f → pr₁ f ≡ b₀))
    eqv22 : (bₙ : B) → (Σ f ꞉ (Σ bₛ ꞉ B , (A → bₙ ≡ bₛ)) , bₙ ≡ b₀) ≃
              (Σ bₛ ꞉ B , Σ f ꞉ (A → bₙ ≡ bₛ) , bₙ ≡ b₀)
    eqv22 bₙ = ≃-sym (Σ-assoc (λ f → bₙ ≡ b₀))
  eqv3 : (Σ bₙ ꞉ B , Σ bₛ ꞉ B , ((A → (bₙ ≡ bₛ)) × (bₙ ≡ b₀))) ≃
           (Σ p ꞉ (Σ bₙ ꞉ B , bₙ ≡ b₀) , Σ bₛ ꞉ B , (A → (pr₁ p ≡ bₛ)))
  eqv3 = eqv31 ≃∙ eqv32 ≃∙ eqv33
   where
    eqv31 : (Σ bₙ ꞉ B , Σ bₛ ꞉ B , ((A → (bₙ ≡ bₛ)) × (bₙ ≡ b₀))) ≃
              (Σ bₙ ꞉ B , (Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ))) × (bₙ ≡ b₀))
    eqv31 = Σ-≃-snd (λ bₙ → Σ-×-assoc B (λ - → A → bₙ ≡ -) (bₙ ≡ b₀))
    eqv32 : (Σ bₙ ꞉ B , (Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ))) × (bₙ ≡ b₀)) ≃
              (Σ bₙ ꞉ B , (bₙ ≡ b₀) × (Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ))))
    eqv32 = Σ-≃-snd (λ bₙ → ×-comm (Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ))) (bₙ ≡ b₀))
    eqv33 : (Σ bₙ ꞉ B , (bₙ ≡ b₀) × (Σ bₛ ꞉ B , (A → (bₙ ≡ bₛ)))) ≃
              (Σ p ꞉ (Σ bₙ ꞉ B , bₙ ≡ b₀) , Σ bₛ ꞉ B , (A → (pr₁ p ≡ bₛ)))
    eqv33 = Σ-assoc (λ p → Σ bₛ ꞉ B , (A → (pr₁ p ≡ bₛ)))
  eqv4 : (Σ p ꞉ (Σ bₙ ꞉ B , bₙ ≡ b₀) , Σ bₛ ꞉ B , (A → (pr₁ p ≡ bₛ))) ≃
           (Σ bₛ ꞉ B , (A → (b₀ ≡ bₛ)))
  eqv4 = isContr-Σ⇒fiber-base (λ p → Σ bₛ ꞉ B , (A → pr₁ p ≡ bₛ))
           (isContr-BasedPaths' b₀)
  eqv5 : (Σ bₛ ꞉ B , (A → (b₀ ≡ bₛ))) ≃
           (Σ bₛ ꞉ B , Σ g ꞉ (A → (b₀ ≡ bₛ)) , Σ q ꞉ (b₀ ≡ bₛ) , g a₀ ≡ q)
  eqv5 =
    Σ-≃-snd (λ bₛ → ≃-sym (isContr-Σ⇒base (λ g → Σ q ꞉ (b₀ ≡ bₛ) , g a₀ ≡ q)
                                 (λ g → isContr-BasedPaths (g a₀))))
  eqv6 : (Σ bₛ ꞉ B , Σ g ꞉ (A → (b₀ ≡ bₛ)) , Σ q ꞉ (b₀ ≡ bₛ) , g a₀ ≡ q) ≃
           (Σ r ꞉ (Σ bₛ ꞉ B , (b₀ ≡ bₛ)) , Σ g ꞉ (A → (b₀ ≡ pr₁ r)) , g a₀ ≡ pr₂ r)
  eqv6 = eqv61 ≃∙ eqv62
   where
    eqv61 : (Σ bₛ ꞉ B , Σ g ꞉ (A → (b₀ ≡ bₛ)) , Σ q ꞉ (b₀ ≡ bₛ) , g a₀ ≡ q) ≃
             (Σ bₛ ꞉ B , Σ q ꞉ (b₀ ≡ bₛ) , Σ g ꞉ (A → (b₀ ≡ bₛ)) , g a₀ ≡ q)
    eqv61 = Σ-≃-snd (λ bₛ → Σ-comm (λ g q → g a₀ ≡ q))
    eqv62 : (Σ bₛ ꞉ B , Σ q ꞉ (b₀ ≡ bₛ) , Σ g ꞉ (A → (b₀ ≡ bₛ)) , g a₀ ≡ q) ≃
              (Σ r ꞉ (Σ bₛ ꞉ B , (b₀ ≡ bₛ)) , Σ g ꞉ (A → (b₀ ≡ pr₁ r)) , g a₀ ≡ pr₂ r)
    eqv62 = Σ-assoc (λ r → Σ g ꞉ (A → b₀ ≡ pr₁ r) , g a₀ ≡ pr₂ r)
  eqv7 : (Σ r ꞉ (Σ bₛ ꞉ B , (b₀ ≡ bₛ)) , Σ g ꞉ (A → (b₀ ≡ pr₁ r)) , g a₀ ≡ pr₂ r) ≃
           (Σ g ꞉ (A → (b₀ ≡ b₀)) , g a₀ ≡ refl b₀)
  eqv7 = isContr-Σ⇒fiber-base
    (λ r → Σ g ꞉ (A → (b₀ ≡ pr₁ r)) , g a₀ ≡ pr₂ r) (isContr-BasedPaths b₀)

N𝕊ⁿ : (n : ℕ) → 𝕊ⁿ n
N𝕊ⁿ 0 = ₁
N𝕊ⁿ (succ n) = N (𝕊ⁿ n)

-- Unnumbered corollary
Map*𝕊ⁿ→-≃Ωⁿ : (n : ℕ) (B : 𝒰∙ 𝒿)
            → Map* (𝕊ⁿ n , N𝕊ⁿ n) B ≃ pr₁ (Ωⁿ n B)
Map*𝕊ⁿ→-≃Ωⁿ 0 B = Map*𝟚→-≃ B
Map*𝕊ⁿ→-≃Ωⁿ (succ n) B = Map*𝝨≃ (𝕊ⁿ n , N𝕊ⁿ n) B ≃∙ (Map*𝕊ⁿ→-≃Ωⁿ n (Ω B))
```

## 6.8 Pushouts
```agda
postulate
  Pushout : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
            (f : C → A) (g : C → B)
          → 𝒰 (𝒾 ⊔ 𝒿 ⊔ 𝓀)
  inl⊔ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
         (f : C → A) (g : C → B)
       → A → Pushout f g
  inr⊔ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
         (f : C → A) (g : C → B)
       → B → Pushout f g
  glue : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
         (f : C → A) (g : C → B)
         (c : C) → inl⊔ f g (f c) ≡ inr⊔ f g (g c)
  Pushout-rec : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀} {D : 𝒰 𝓁}
                (f : C → A) (g : C → B)
              → (inl' : A → D)
              → (inr' : B → D)
              → ((c : C) → inl' (f c) ≡ inr' (g c))
              → Pushout f g → D
  Pushout-rec-comp-inl :
        {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀} {D : 𝒰 𝓁}
        (f : C → A) (g : C → B)
      → (inl' : A → D)
      → (inr' : B → D)
      → (glue' : ((c : C) → inl' (f c) ≡ inr' (g c)))
      → (a : A) → Pushout-rec f g inl' inr' glue' (inl⊔ f g a) ≡ inl' a
  {-# REWRITE Pushout-rec-comp-inl #-}
  Pushout-rec-comp-inr :
        {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀} {D : 𝒰 𝓁}
        (f : C → A) (g : C → B)
      → (inl' : A → D)
      → (inr' : B → D)
      → (glue' : ((c : C) → inl' (f c) ≡ inr' (g c)))
      → (b : B) → Pushout-rec f g inl' inr' glue' (inr⊔ f g b) ≡ inr' b
  {-# REWRITE Pushout-rec-comp-inr #-}
  Pushout-rec-comp : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀} {D : 𝒰 𝓁}
                     (f : C → A) (g : C → B)
                   → (inl' : A → D)
                   → (inr' : B → D)
                   → (glue' : ((c : C) → inl' (f c) ≡ inr' (g c)))
                   → (c : C) → ap (Pushout-rec f g inl' inr' glue') (glue f g c) ≡ glue' c

  -- Omitted induction principle
  Pushout-ind : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
                (f : C → A) (g : C → B) {P : Pushout f g → 𝒰 𝓁}
              → (inl' : (a : A) → P (inl⊔ f g a))
              → (inr' : (b : B) → P (inr⊔ f g b))
              → ((c : C) → tr P (glue f g c) (inl' (f c)) ≡ inr' (g c))
              → (p : Pushout f g) → P p
  Pushout-ind-comp-inl :
        {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
        (f : C → A) (g : C → B) {P : Pushout f g → 𝒰 𝓁}
      → (inl' : (a : A) → P (inl⊔ f g a))
      → (inr' : (b : B) → P (inr⊔ f g b))
      → (glue' : ((c : C) → tr P (glue f g c) (inl' (f c)) ≡ inr' (g c)))
      → (a : A) → Pushout-ind f g inl' inr' glue' (inl⊔ f g a) ≡ inl' a
  {-# REWRITE Pushout-ind-comp-inl #-}
  Pushout-ind-comp-inr :
        {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
        (f : C → A) (g : C → B) {P : Pushout f g → 𝒰 𝓁}
      → (inl' : (a : A) → P (inl⊔ f g a))
      → (inr' : (b : B) → P (inr⊔ f g b))
      → (glue' : ((c : C) → tr P (glue f g c) (inl' (f c)) ≡ inr' (g c)))
      → (b : B) → Pushout-ind f g inl' inr' glue' (inr⊔ f g b) ≡ inr' b
  {-# REWRITE Pushout-ind-comp-inr #-}
  Pushout-ind-comp :
        {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
        (f : C → A) (g : C → B) {P : Pushout f g → 𝒰 𝓁}
      → (inl' : (a : A) → P (inl⊔ f g a))
      → (inr' : (b : B) → P (inr⊔ f g b))
      → (glue' : ((c : C) → tr P (glue f g c) (inl' (f c)) ≡ inr' (g c)))
      → (c : C) → apd (Pushout-ind f g inl' inr' glue') (glue f g c) ≡ glue' c
```

## 6.9 Truncations

```agda
postulate
  ∥_∥₀ : {𝒾 : Level} → (A : 𝒰 𝒾) → 𝒰 𝒾
  ∣_∣₀ : {𝒾 : Level} → {A : 𝒰 𝒾} → A → ∥ A ∥₀
  ∥∥₀-isSet : {X : 𝒰 𝒾} → isSet (∥ X ∥₀)
  ∥∥₀-rec : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
          → isSet B
          → (g : A → B)
          → ∥ A ∥₀ → B
  ∥∥₀-rec-comp : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
               → (p : isSet B)
               → (g : A → B)
               → (a : A)
               → ∥∥₀-rec A B p g (∣ a ∣₀) ≡ g a
  {-# REWRITE ∥∥₀-rec-comp #-}
  ∥∥₀-ind : (A : 𝒰 𝒾) (B : ∥ A ∥₀ → 𝒰 𝒿)
          → ((x y : ∥ A ∥₀) (z : B x) (w : B y)
             (p q : x ≡ y) (r : tr B p z ≡ w) (s : tr B q z ≡ w)
             → r ≡ tr² B (∥∥₀-isSet p q) z ∙ s)
          → (g : (a : A) → B (∣ a ∣₀))
          → ((x : ∥ A ∥₀) → B x)
  ∥∥₀-ind-comp : (A : 𝒰 𝒾) (B : ∥ A ∥₀ → 𝒰 𝒿)
              → (Bsetish : (x y : ∥ A ∥₀) (z : B x) (w : B y)
                 (p q : x ≡ y) (r : tr B p z ≡ w) (s : tr B q z ≡ w)
                 → r ≡ tr² B (∥∥₀-isSet p q) z ∙ s)
              → (g : (a : A) → B (∣ a ∣₀))
              → (x y : ∥ A ∥₀) (z : B x) (w : B y)
                 (p q : x ≡ y)
              → apd² (∥∥₀-ind A B Bsetish g) (∥∥₀-isSet p q) ≡ Bsetish x y
                 ((∥∥₀-ind A B Bsetish g) x) ((∥∥₀-ind A B Bsetish g) y) p q
                  (apd (∥∥₀-ind A B Bsetish g) p) (apd (∥∥₀-ind A B Bsetish g) q)
  -- {-# REWRITE ∥∥₀-ind-comp #-}

-- Lemma 6.9.1.
∥∥₀-family-of-sets : (A : 𝒰 𝒾) (B : ∥ A ∥₀ → 𝒰 𝒿)
                   → ((a : A) → B (∣ a ∣₀))
                   → ((x : ∥ A ∥₀) → isSet (B x))
                   → ((x : ∥ A ∥₀) → B x)
∥∥₀-family-of-sets A B g BxIsSet =
  ∥∥₀-ind A B (λ x y z w p q r s → BxIsSet y r (tr² B (∥∥₀-isSet p q) z ∙ s)) g
```

## 6.10 Quotients

```agda
mereRelation : {𝒾 : Level} (A : 𝒰 𝒾) (𝒿 : Level) → 𝒰 (𝒾 ⊔ (𝒿 ⁺))
mereRelation A 𝒿 = A × A → Prop𝒰 𝒿

postulate
  _∕_ : (A : 𝒰 𝒾) (R : mereRelation A 𝒿) → 𝒰 (𝒾 ⊔ (𝒿 ⁺))
  quot : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
       → A → (A ∕ R)
  quot≡ : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
        → (a b : A) → (pr₁ (R (a , b)))
        → (quot A R a ≡ quot A R b)
  ∕-isSet : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
          → isSet (A ∕ R)
  ∕-rec : (A : 𝒰 𝒾) (R : mereRelation A 𝒿) (B : 𝒰 𝓀)
        → (f : A → B)
        → ((a b : A) → (pr₁ (R (a , b))) → f a ≡ f b)
        → A ∕ R → B
  ∕-rec-comp : (A : 𝒰 𝒾) (R : mereRelation A 𝒿) (B : 𝒰 𝓀)
             → (f : A → B)
             → (p : ((a b : A) → (pr₁ (R (a , b))) → f a ≡ f b))
             → (a : A)
             → ∕-rec A R B f p (quot A R a) ≡ f a
  {-# REWRITE ∕-rec-comp #-}
  ∕-ind : (A : 𝒰 𝒾) (R : mereRelation A 𝒿) (B : A ∕ R → 𝒰 𝓀)
        → (f : (a : A) → B (quot A R a))
        → ((a b : A) → (resp : pr₁ (R (a , b)))
           → tr B (quot≡ A R a b resp) (f a) ≡ f b)
        → ((x : A ∕ R) → B x)

infixr 30 _∕_

-- Lemma 6.10.2.
isSurjec-quot : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
              → isSurjec (quot A R)
isSurjec-quot A R = ∕-ind A R (λ z → ∥ fib (quot A R) z ∥) f f-respects-R
  where
    f : (a : A) → ∥ fib (quot A R) (quot A R a) ∥
    f a = ∣ a , refl (quot A R a) ∣
    f-respects-R : (a b : A) → (resp : pr₁ (R (a , b)))
                 → tr (λ z → ∥ fib (λ a₁ → quot A R a₁) z ∥)
                       (quot≡ A R a b resp) (f a) ≡ f b
    f-respects-R a b resp = ∥∥-isProp _ _

-- Lemma 6.10.3.
∕→-≃ : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
       (B : 𝒰 𝓀) → isSet B
     → (A ∕ R → B) ≃ (Σ f ꞉ (A → B) , ((a b : A) → pr₁ (R (a , b)) → f a ≡ f b))
∕→-≃ A R B isSet-B = φ , invs⇒equivs φ (φ⁻¹ , ε , η)
  where
    φ = λ - → (- ∘ (quot A R) , λ a b p → ap - (quot≡ A R a b p))
    φ⁻¹ : (Σ f ꞉ (A → B) , ((a b : A) → pr₁ (R (a , b)) → f a ≡ f b))
        → (A ∕ R → B)
    φ⁻¹ (f , p) = ∕-rec A R B f p
    ε : φ ∘ φ⁻¹ ∼ id
    ε (f , p) =
      pair⁼(refl _ , funext (λ a → funext
                                       (λ b → funext (λ r → isSet-B _ _))))
    η = λ g → funext
                (λ x → ∥∥-rec (fib (quot A R) x)
                (φ⁻¹ (φ g) x ≡ g x)
                (isSet-B)
                (λ (a , p) → begin
                  φ⁻¹ (φ g) x ≡˘⟨ ap (φ⁻¹ (φ g)) p ⟩
                  φ⁻¹ (φ g) (quot A R a) ≡⟨ refl _ ⟩
                  g (quot A R a) ≡⟨ ap g p ⟩
                  g x ∎)
                (isSurjec-quot A R x))

reflexive
 symmetric
 transitive
 equivalenceRelation : {X : 𝒰 𝒾} → (X → X → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)

reflexive  _≈_ = ∀ x → x ≈ x
symmetric  _≈_ = ∀ x y → x ≈ y → y ≈ x
transitive _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

equivalenceRelation _≈_ = reflexive _≈_
                        × symmetric _≈_
                        × transitive _≈_

-- Definition 6.10.4.
_isEquivalenceClassOf_ : {A : 𝒰 𝒾}
                         (P : A → Prop𝒰 𝒿) (R : mereRelation A 𝓀)
                       → 𝒰 (𝒾 ⊔ 𝒿 ⊔ 𝓀)
P isEquivalenceClassOf R =
  ∥ Σ a ꞉ (domain P) ,
    ((b : (domain P)) → pr₁ (R (a , b)) ≃ pr₁ (P b)) ∥

-- Definition 6.10.5.
_∕∕_ : {𝒾 𝒿 : Level}
       (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
     → 𝒰 (𝒾 ⊔ (𝒿 ⁺))
(_∕∕_) {𝒾} {𝒿} A R = Σ P ꞉ (A → Prop𝒰 𝒿) , P isEquivalenceClassOf R

quot' : {𝒾 𝒿 : Level}
        (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
      → A → (A ∕∕ R)
quot' A R a = (λ b → R(a , b)) , ∣ a , (λ b → ≃-refl _) ∣

quot'-isSurjec : {𝒾 𝒿 : Level}
      → (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
      → isSurjec (quot' A R)
quot'-isSurjec A R P = ∥∥-rec _ _ ∥∥-isProp fibInh (pr₂ P)
 where
  fibInh : -Σ A (λ a → (b : A) → pr₁ (R (a , b)) ≃ pr₁ (pr₁ P b)) →
           ∥ Σ x ꞉ A , (quot' A R) x ≡ P ∥
  fibInh (a , f) =
   ∣ a ,
     pair⁼(
       funext (λ b →
         pair⁼(
           ua (isProp-areLogEq⇒Eq _ _ (pr₂ (R (a , b))) (pr₂ (pr₁ P b))
                (≃-→ (f b))
                (≃-← (f b)))
         , funext
             (λ x → funext (λ y → isProp⇒isSet (pr₂ (pr₁ P b)) _ _))))
     , ∥∥-isProp _ _) ∣

-- This can be proven, but has not been done so in the book, so I won't either.
postulate
  ∕∕-isSet : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
           → isSet (A ∕∕ R)

∕∕≃∕ : {𝒾 𝒿 : Level}
     → (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
     → (equivalenceRelation (λ a b → pr₁ (R (a , b))))
     → (A ∕ R) ≃ (A ∕∕ R)
∕∕≃∕ A R eR =
  f , isSurj-isEmbedding⇒isEquiv f isSurjec-f isEmbedding-f
 where
  f : A ∕ R → A ∕∕ R
  f = ∕-rec A R (A ∕∕ R) (quot' A R) quot'-preserves-R
   where
    lemma : (a b c : A) → pr₁ (R(a , b)) → pr₁ (R(a , c)) → pr₁ (R(b , c))
    lemma a b c aRb aRc =  pr₂ (pr₂ eR) b a c (pr₁ (pr₂ eR) a b aRb) aRc
    quot'-preserves-R : (a b : A) (r : pr₁ (R (a , b)))
                      → (quot' A R a) ≡ (quot' A R b)
    quot'-preserves-R a b aRb  =
     pair⁼(
      funext (λ c → (pair⁼(
        ua (isProp-areLogEq⇒Eq _ _ (pr₂ (R (a , c))) (pr₂ (R (b , c)))
             (λ aRc → lemma a b c aRb aRc)
             (λ bRc → lemma b a c (pr₁ (pr₂ eR) a b aRb) bRc))
        , funext (λ x → funext (λ y → isProp⇒isSet (pr₂ (R(b , c))) _ _)))))
      , ∥∥-isProp _ _)
  isSurjec-f : (b : (A ∕∕ R)) → ∥ fib f b ∥
  isSurjec-f (P , PeR) =
    ∥∥-rec _ _ ∥∥-isProp
      (λ (a , p) → ∣ quot A R a , p ∣)
      (quot'-isSurjec A R (P , PeR))
  isInjec-f : isInjective f
  isInjec-f x y fx≡fy =
    ∥∥-rec _ _ (∕-isSet A R)
      (λ (a , p) →
        ∥∥-rec _ _ (∕-isSet A R)
          (λ (b , q) →
            p ⁻¹ ∙
              quot≡ A R a b
                (tr id (ap pr₁
                          (happly (ap pr₁ ((ap f p)
                            ∙ fx≡fy
                            ∙ (ap f (q ⁻¹)))) b)⁻¹)
                       (pr₁ eR b)) ∙
              q )
          (isSurjec-quot A R y))
      (isSurjec-quot A R x)
  isEmbedding-f : isEmbedding f
  isEmbedding-f =
    isSet-isInjective⇒isEmbedding (∕-isSet A R) (∕∕-isSet A R) f isInjec-f

idempotent : {A : 𝒰 𝒾}
             (r : A → A)
           → 𝒰 𝒾
idempotent r = r ∘ r ≡ r

-- Lemma 6.10.8.
∕∼→-≃ : (A : 𝒰 𝒾)
      → isSet A
      → (∼ : mereRelation A 𝒿)
        (r : A → A)
      → idempotent r
      → ((x y : A) → (r x ≡ r y) ≃ pr₁ (∼ (x , y)))
      → (B : 𝒰 𝓀)
      → isSet B
      → ((Σ x ꞉ A , r x ≡ x) → B) ≃
          (Σ g ꞉ (A → B) , ((x y : A) → pr₁ (∼ (x , y)) → g x ≡ g y))
∕∼→-≃ A isSet-A ∼ r i r-reflects-~ B isSet-B =
  e , invs⇒equivs e (e' , ε , η)
 where
  𝓆 : A → (Σ x ꞉ A , r x ≡ x)
  𝓆 x = (r x , happly i x)
  e = λ f → (f ∘ 𝓆 , λ x y p →
         ap f (pair⁼(≃-← (r-reflects-~ x y) p , isSet-A _ _)))
  e' = λ (g , s) → λ (x , p) → g x
  η = λ f → funext (λ (x , p) → ap f (pair⁼(p , isSet-A _ _)))
  ε = λ (g , s) →
    pair⁼(
      funext (λ x → s (r x) x (≃-→ (r-reflects-~ (r x) x) (happly i x))) ,
      funext λ - → funext (λ - → funext (λ - → isSet-B _ _)))

-- Definitions and lemmas for definition of ℤ
data _≤_ : ℕ → ℕ → 𝒰₀ where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → succ m ≤ succ n
infix 4 _≤_

¬s≤z : ∀ {m : ℕ} → ¬ (succ m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (succ m ≤ succ n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

sn≤sm⇒n≤m : {m n : ℕ} → (succ m ≤ succ n) → (m ≤ n)
sn≤sm⇒n≤m (s≤s p) = p

n≤z→n≡0 : (n : ℕ) → n ≤ 0 → n ≡ 0
n≤z→n≡0 zero e = refl zero
n≤z→n≡0 (succ n) e = !𝟘 _ (¬s≤z e)

isDecidable-≤ : (n m : ℕ) → isDecidable (n ≤ m)
isDecidable-≤ zero m = inl z≤n
isDecidable-≤ (succ n) zero = inr ¬s≤z
isDecidable-≤ (succ n) (succ m) =
  ⊎-rec (isDecidable (succ n ≤ succ m))
    (λ - → inl (s≤s -))
    (λ - → inr (¬s≤s -))
    (isDecidable-≤ n m)

_∸_ : ℕ → ℕ → ℕ
n      ∸ zero = n
zero   ∸ succ m = zero
succ n ∸ succ m = n ∸ m
infixl 6 _∸_

{-# BUILTIN NATMINUS _∸_ #-}

rℕ : ℕ × ℕ → ℕ × ℕ
rℕ (a , b) =
  ⊎-rec (ℕ × ℕ)
    (λ _ → ((a ∸ b) , 0))
    (λ _ → (0 , (b ∸ a)))
    (isDecidable-≤ b a)

rℕ-≡ : (m n : ℕ)
     → (rℕ (m , n) ≡ ((m ∸ n) , 0)) ⊎ (rℕ (m , n) ≡ (0 , (n ∸ m)))
rℕ-≡ m n =
  ⊎-ind (λ - → (
    (⊎-rec (ℕ × ℕ)
      (λ _ → ((m ∸ n) , 0))
      (λ _ → (0 , (n ∸ m))) -) ≡ ((m ∸ n) , 0)) ⊎ (
    (⊎-rec (ℕ × ℕ)
      (λ _ → ((m ∸ n) , 0))
      (λ _ → (0 , (n ∸ m))) -) ≡ (0 , (n ∸ m))))
    (λ _ → inl (refl _))
    (λ _ → inr (refl _))
    (isDecidable-≤ n m)

rℕ-¬succ : (m n : ℕ) → ¬ (rℕ (succ m , succ n) ≡ (succ m , succ n))
rℕ-¬succ m n p =
  (⊎-rec _
    (λ e → ¬0≡succ n (ap pr₂ (e ⁻¹ ∙ p)))
    (λ e → ¬0≡succ m (ap pr₁ (e ⁻¹ ∙ p)))
    (rℕ-≡ (succ m) (succ n)))

rℕ-succ : (n m : ℕ) → rℕ (n , m) ≡ rℕ (succ n , succ m)
rℕ-succ a b =
  ⊎-ind (λ - → (
    ⊎-rec (ℕ × ℕ)
      (λ _ → ((a ∸ b) , 0))
      (λ _ → (0 , (b ∸ a))) -) ≡ rℕ (succ a , succ b))
    (λ p →
       ⊎-ind (λ - → ((a ∸ b) , 0) ≡ (
         ⊎-rec (ℕ × ℕ)
           (λ _ → ((succ a ∸ succ b) , 0))
           (λ _ → (0 , (succ b ∸ succ a))) -))
         (λ - → refl _)
         (λ - → !𝟘 _ (- (s≤s p)))
         (isDecidable-≤ (succ b) (succ a)))
    (λ p →
       ⊎-ind (λ - → (0 , (b ∸ a)) ≡
         ⊎-rec (ℕ × ℕ)
           (λ _ → ((succ a ∸ succ b) , 0))
           (λ _ → (0 , (succ b ∸ succ a))) -)
         (λ - → !𝟘 _ (p (sn≤sm⇒n≤m -)))
         (λ - → refl (zero , (b ∸ a)))
         (isDecidable-≤ (succ b) (succ a)))
    (isDecidable-≤ b a)

rℕ-left-0 : (n : ℕ) → rℕ (0 , n) ≡ (0 , n)
rℕ-left-0 n =
  ⊎-ind (λ - → (
    ⊎-rec (ℕ × ℕ)
      (λ _ → ((0 ∸ n) , 0))
      (λ _ → (0 , (n ∸ 0))) -) ≡ (0 , n))
    (λ e → tr (λ - → (0 ∸ -) , 0 ≡ 0 , -) (n≤z→n≡0 n e ⁻¹) (refl _))
    (λ _ → refl _)
    (isDecidable-≤ n 0)

rℕ-right-0 : (n : ℕ) → rℕ (n , 0) ≡ (n , 0)
rℕ-right-0 n =
  ⊎-ind (λ - → (
    ⊎-rec (ℕ × ℕ)
      (λ _ → ((n ∸ 0) , 0))
      (λ _ → (0 , (0 ∸ n))) -) ≡ (n , 0))
    (λ _ → refl _)
    (λ e → !𝟘 _ (e z≤n))
    (isDecidable-≤ 0 n)

idempotent-rℕ : idempotent rℕ
idempotent-rℕ = funext lemma
 where
  lemma : rℕ ∘ rℕ ∼ rℕ
  lemma (a , b) =
   ⊎-ind (λ - → rℕ ((
    ⊎-rec (ℕ × ℕ)
      (λ _ → ((a ∸ b) , 0))
      (λ _ → (0 , (b ∸ a))) -)) ≡
      (⊎-rec (ℕ × ℕ)
        (λ _ → ((a ∸ b) , 0))
        (λ _ → (0 , (b ∸ a))) -))
     (λ - → refl ((a ∸ b) , zero))
     (λ - → rℕ-left-0 _)
     (isDecidable-≤ b a)

ℤ : 𝒰₀
ℤ = Σ x ꞉ (ℕ × ℕ) , (rℕ x ≡ x)

0ℤ : ℤ
0ℤ = (0 , 0) , refl _

ℕ-in-ℤ≥0 : ℕ → ℤ
ℕ-in-ℤ≥0 n = (n , 0) , rℕ-right-0 n

ℕ-in-ℤ≤0 : ℕ → ℤ
ℕ-in-ℤ≤0 n = (0 , n) , rℕ-left-0 n

isSet-ℕ×ℕ : isSet (ℕ × ℕ)
isSet-ℕ×ℕ = isSet-× isSet-ℕ isSet-ℕ

isSet-ℤ : isSet ℤ
isSet-ℤ =
  isSet-Σ
    isSet-ℕ×ℕ
    (λ - → isSet⇒is1Type (isSet-Σ isSet-ℕ λ - → isSet-ℕ ))

-- Lemma 6.10.12.
ℤ-ind-full : (P : ℤ → 𝒰 𝒾)
             (d₀ : P 0ℤ)
             (d₊ : (n : ℕ) → P (ℕ-in-ℤ≥0 n) → P (ℕ-in-ℤ≥0 (succ n)))
             (d₋ : (n : ℕ) → P (ℕ-in-ℤ≤0 n) → P (ℕ-in-ℤ≤0 (succ n)))
           → Σ f ꞉ ((z : ℤ ) → P z) ,
              (f 0ℤ ≡ d₀) ×
              ((n : ℕ) → f (ℕ-in-ℤ≥0 (succ n)) ≡ d₊ n (f (ℕ-in-ℤ≥0 n))) ×
              ((n : ℕ) → f (ℕ-in-ℤ≤0 (succ n)) ≡ d₋ n (f (ℕ-in-ℤ≤0 n)))
ℤ-ind-full P d₀ d₊ d₋ = (f , f0 , fn⁺ , fn⁻)
 where
  𝓆 : (ℕ × ℕ) → ℤ
  𝓆 x = (rℕ x , happly idempotent-rℕ x)
  Q : ℕ × ℕ → 𝒰 _
  Q = P ∘ 𝓆

  d₀'-path : 0ℤ ≡ 𝓆 (0 , 0)
  d₀'-path = pair⁼(refl _ , isSet-ℕ×ℕ _ _)
  d₀' : Q (0 , 0)
  d₀' = tr P d₀'-path d₀

  d₊'-path1 : (n : ℕ) → ℕ-in-ℤ≥0 (succ n) ≡ 𝓆 (succ n , 0)
  d₊'-path1 n = pair⁼(refl _ , (isSet-ℕ×ℕ _ _))
  d₊'-path2 : (n : ℕ) → 𝓆 (n , 0) ≡ ℕ-in-ℤ≥0 n
  d₊'-path2 n = pair⁼(refl _ , (isSet-ℕ×ℕ _ (rℕ-right-0 n)))
  d₊' : (n : ℕ) → Q (n , 0) → Q (succ n , 0)
  d₊' n p = tr P (d₊'-path1 n) (d₊ n (tr P (d₊'-path2 n) p))

  d₋'-path1 : (n : ℕ) → ℕ-in-ℤ≤0 (succ n) ≡ 𝓆 (0 , succ n)
  d₋'-path1 n = pair⁼(rℕ-left-0 (succ n) , isSet-ℕ×ℕ _ _)⁻¹
  d₋'-path2 : (n : ℕ) → 𝓆 (0 , n) ≡ ℕ-in-ℤ≤0 n
  d₋'-path2 n = pair⁼(rℕ-left-0 n , isSet-ℕ×ℕ _ _)
  d₋' : (n : ℕ) → Q (0 , n) → Q (0 , succ n)
  d₋' n p = tr P (d₋'-path1 n) (d₋ n (tr P (d₋'-path2 n) p))

  𝓆-succ : (n m : ℕ) → 𝓆 (n , m) ≡ 𝓆 (succ n , succ m)
  𝓆-succ n m = pair⁼(rℕ-succ n m  , isSet-ℕ×ℕ _ _)
  g : (x : ℕ × ℕ) → Q x
  g (zero , zero) = d₀'
  g (succ n , zero) = d₊' n (g (n , 0))
  g (zero , succ m) = d₋' m (g (0 , m))
  g (succ n , succ m) = tr id (ap P (𝓆-succ n m)) (g (n , m))

  f-path : (z : ℤ) → 𝓆 (pr₁ z) ≡ z
  f-path z = pair⁼(pr₂ z , isSet-ℕ×ℕ _ _)
  f : (z : ℤ) → P z
  f z = tr P (f-path z) (g (pr₁ z))

  f0 : f 0ℤ ≡ d₀
  f0 = begin
    tr P (f-path 0ℤ) (tr P d₀'-path d₀) ≡⟨ i ⟩
    tr P (d₀'-path ∙ f-path 0ℤ) d₀      ≡⟨ ii ⟩
    d₀ ∎
   where
    i = happly (tr-∘ P d₀'-path (f-path 0ℤ)) d₀
    ii = ap (λ - → tr P - d₀) (isSet-ℤ (d₀'-path ∙ f-path 0ℤ) (refl _))

  fn⁻ : (n : ℕ) → f (ℕ-in-ℤ≤0 (succ n)) ≡ d₋ n (f (ℕ-in-ℤ≤0 n))
  fn⁻ n = begin
     tr P (f-path (ℕ-in-ℤ≤0 (succ n)))
        (tr P (d₋'-path1 n)
          (d₋ n (tr P (d₋'-path2 n) (g (0 , n)))))  ≡⟨ i ⟩
     tr P ((d₋'-path1 n)
             ∙ (f-path (ℕ-in-ℤ≤0 (succ n))))
          (d₋ n (tr P (d₋'-path2 n) (g (0 , n))))  ≡⟨ ii ⟩
      d₋ n (tr P (d₋'-path2 n) (g (0 , n)))   ∎
   where
    i = happly (tr-∘ P (d₋'-path1 n) (f-path (ℕ-in-ℤ≤0 (succ n))))
         (d₋ n (tr P (d₋'-path2 n) (g (0 , n))))
    ii = ap (λ - → tr P - (d₋ n (tr P (d₋'-path2 n) (g (0 , n)))))
            (isSet-ℤ ((d₋'-path1 n) ∙ (f-path (ℕ-in-ℤ≤0 (succ n)))) (refl _))

  fn⁺ : (n : ℕ) → f (ℕ-in-ℤ≥0 (succ n)) ≡ d₊ n (f (ℕ-in-ℤ≥0 n))
  fn⁺ n = begin
     tr P (f-path (ℕ-in-ℤ≥0 (succ n)))
        (tr P (d₊'-path1 n)
          (d₊ n (tr P (d₊'-path2 n) (g (n , 0)))))  ≡⟨ i ⟩
     tr P ((d₊'-path1 n)
             ∙ (f-path (ℕ-in-ℤ≥0 (succ n))))
          (d₊ n (tr P (d₊'-path2 n) (g (n , 0))))   ≡⟨ ii ⟩
      d₊ n (tr P (d₊'-path2 n) (g (n , 0)))   ∎
   where
    i = happly (tr-∘ P (d₊'-path1 n) (f-path (ℕ-in-ℤ≥0 (succ n))))
         (d₊ n (tr P (d₊'-path2 n) (g (n , 0))))
    ii = ap (λ - → tr P - (d₊ n (tr P (d₊'-path2 n) (g (n , 0)))))
            (isSet-ℤ ((d₊'-path1 n) ∙ (f-path (ℕ-in-ℤ≥0 (succ n)))) (refl _))

ℤ-ind : (P : ℤ → 𝒰 𝒾)
        (d₀ : P 0ℤ)
        (d₊ : (n : ℕ) → P (ℕ-in-ℤ≥0 n) → P (ℕ-in-ℤ≥0 (succ n)))
        (d₋ : (n : ℕ) → P (ℕ-in-ℤ≤0 n) → P (ℕ-in-ℤ≤0 (succ n)))
      → (z : ℤ ) → P z
ℤ-ind P d₀ d₊ d₋ =
  let (f , f0 , fn⁺ , fn⁻) = ℤ-ind-full P d₀ d₊ d₋
   in f

ℤ-ind-comp-0ℤ :
        (P : ℤ → 𝒰 𝒾)
        (d₀ : P 0ℤ)
        (d₊ : (n : ℕ) → P (ℕ-in-ℤ≥0 n) → P (ℕ-in-ℤ≥0 (succ n)))
        (d₋ : (n : ℕ) → P (ℕ-in-ℤ≤0 n) → P (ℕ-in-ℤ≤0 (succ n)))
      → ℤ-ind P d₀ d₊ d₋ 0ℤ ≡ d₀
ℤ-ind-comp-0ℤ P d₀ d₊ d₋ =
  let (f , f0 , fn⁺ , fn⁻) = ℤ-ind-full P d₀ d₊ d₋
   in f0

ℤ-ind-comp-ℤ≥0 :
        (P : ℤ → 𝒰 𝒾)
        (d₀ : P 0ℤ)
        (d₊ : (n : ℕ) → P (ℕ-in-ℤ≥0 n) → P (ℕ-in-ℤ≥0 (succ n)))
        (d₋ : (n : ℕ) → P (ℕ-in-ℤ≤0 n) → P (ℕ-in-ℤ≤0 (succ n)))
      → ((n : ℕ) → ℤ-ind P d₀ d₊ d₋ (ℕ-in-ℤ≥0 (succ n))
                 ≡ d₊ n (ℤ-ind P d₀ d₊ d₋ (ℕ-in-ℤ≥0 n)))
ℤ-ind-comp-ℤ≥0 P d₀ d₊ d₋ =
  let (f , f0 , fn⁺ , fn⁻) = ℤ-ind-full P d₀ d₊ d₋
   in fn⁺

ℤ-ind-comp-ℤ≤0 :
        (P : ℤ → 𝒰 𝒾)
        (d₀ : P 0ℤ)
        (d₊ : (n : ℕ) → P (ℕ-in-ℤ≥0 n) → P (ℕ-in-ℤ≥0 (succ n)))
        (d₋ : (n : ℕ) → P (ℕ-in-ℤ≤0 n) → P (ℕ-in-ℤ≤0 (succ n)))
      → ((n : ℕ) → ℤ-ind P d₀ d₊ d₋ (ℕ-in-ℤ≤0 (succ n))
                    ≡ d₋ n (ℤ-ind P d₀ d₊ d₋ (ℕ-in-ℤ≤0 n)))
ℤ-ind-comp-ℤ≤0 P d₀ d₊ d₋ =
  let (f , f0 , fn⁺ , fn⁻) = ℤ-ind-full P d₀ d₊ d₋
   in fn⁻

-- Helpers for the non-dependent case
ℤ-rec : (B : 𝒰 𝒾)
        (d₀ : B)
        (d₊ : B → B)
        (d₋ : B → B)
      → ℤ → B
ℤ-rec B d₀ d₊ d₋ = ℤ-ind (λ _ → B) d₀ (λ _ → d₊) (λ _ → d₋)

ℤ-rec-comp-0ℤ :
        (B : 𝒰 𝒾)
        (d₀ : B)
        (d₊ : B → B)
        (d₋ : B → B)
      → ℤ-rec B d₀ d₊ d₋ 0ℤ ≡ d₀
ℤ-rec-comp-0ℤ B d₀ d₊ d₋ = ℤ-ind-comp-0ℤ (λ _ → B) d₀ (λ _ → d₊) (λ _ → d₋)

ℤ-rec-comp-ℤ≥0 :
        (B : 𝒰 𝒾)
        (d₀ : B)
        (d₊ : B → B)
        (d₋ : B → B)
      → ((n : ℕ) → ℤ-rec B d₀ d₊ d₋ (ℕ-in-ℤ≥0 (succ n))
                    ≡ d₊ (ℤ-rec B d₀ d₊ d₋ (ℕ-in-ℤ≥0 n)))
ℤ-rec-comp-ℤ≥0 B d₀ d₊ d₋ =
  ℤ-ind-comp-ℤ≥0 (λ _ → B) d₀ (λ _ → d₊) (λ _ → d₋)

ℤ-rec-comp-ℤ≤0 :
        (B : 𝒰 𝒾)
        (d₀ : B)
        (d₊ : B → B)
        (d₋ : B → B)
      → ((n : ℕ) → ℤ-rec B d₀ d₊ d₋ (ℕ-in-ℤ≤0 (succ n))
                    ≡ d₋ (ℤ-rec B d₀ d₊ d₋ (ℕ-in-ℤ≤0 n)))
ℤ-rec-comp-ℤ≤0 B d₀ d₊ d₋ =
  ℤ-ind-comp-ℤ≤0 (λ _ → B) d₀ (λ _ → d₊) (λ _ → d₋)

-- Lemmas to use for the induction and recursion computation rules
ℤ-<0∨≥0 : (z : ℤ) → (Σ n ꞉ ℕ , z ≡ (ℕ-in-ℤ≤0 (succ n))) ⊎ (Σ n ꞉ ℕ , z ≡ ℕ-in-ℤ≥0 n)
ℤ-<0∨≥0 ((zero , zero) , p)     = inr (0 , pair⁼ (refl (zero , zero) , isSet-ℕ×ℕ _ _))
ℤ-<0∨≥0 ((zero , succ b) , p)   = inl (b , pair⁼(refl _ , isSet-ℕ×ℕ _ _))
ℤ-<0∨≥0 ((succ a , zero) , p)   = inr (succ a , pair⁼(refl _ , isSet-ℕ×ℕ _ _))
ℤ-<0∨≥0 ((succ a , succ b) , p) = !𝟘 _ (rℕ-¬succ a b p)

ℤ-≤0∨>0 : (z : ℤ) → (Σ n ꞉ ℕ , z ≡ (ℕ-in-ℤ≤0 n)) ⊎ (Σ n ꞉ ℕ , z ≡ ℕ-in-ℤ≥0 (succ n))
ℤ-≤0∨>0 ((zero , zero) , p)     = inl (0 , pair⁼ (refl (zero , zero) , isSet-ℕ×ℕ _ _))
ℤ-≤0∨>0 ((zero , succ b) , p)   = inl (succ b , pair⁼(refl _ , isSet-ℕ×ℕ _ _))
ℤ-≤0∨>0 ((succ a , zero) , p)   = inr (a , pair⁼(refl _ , isSet-ℕ×ℕ _ _))
ℤ-≤0∨>0 ((succ a , succ b) , p) = !𝟘 _ (rℕ-¬succ a b p)

-- Define the succ function for integers
succ-ℤ : ℤ → ℤ
succ-ℤ ((zero , zero) , p)     = ((1 , 0) , refl (1 , 0))
succ-ℤ ((zero , succ b) , p)   = ((0 , b) , rℕ-left-0 b)
succ-ℤ ((succ a , zero) , p)   = ((succ (succ a) , 0) , rℕ-right-0 (succ (succ a)))
succ-ℤ ((succ a , succ b) , p) = !𝟘 ℤ (rℕ-¬succ a b p)

pred-ℤ : ℤ → ℤ
pred-ℤ ((zero , zero) , p)     = ((0 , 1) , refl (0 , 1))
pred-ℤ ((zero , succ b) , p)   = ((0 , succ (succ b)) , rℕ-left-0 (succ (succ b)))
pred-ℤ ((succ a , zero) , p)   = ((a , 0) , rℕ-right-0 a)
pred-ℤ ((succ a , succ b) , p) = !𝟘 ℤ (rℕ-¬succ a b p)

-- Succ is an equivalence
succ-ℤ-≃ : ℤ ≃ ℤ
succ-ℤ-≃ = succ-ℤ , invs⇒equivs succ-ℤ (pred-ℤ , ε , η)
 where
  ε-lemma : (a : ℕ) (p : rℕ(a , 0) ≡ (a , 0))
          → (succ-ℤ ∘ pred-ℤ) ((a , 0) , p) ≡ ((a , 0) , p)
  ε-lemma zero p            = pair⁼ (refl (zero , zero) , isSet-ℕ×ℕ _ _)
  ε-lemma (succ zero) p     = pair⁼ (refl (1 , zero) , isSet-ℕ×ℕ _ _)
  ε-lemma (succ (succ a)) p = pair⁼ (refl (succ (succ a) , zero) , isSet-ℕ×ℕ _ _)

  η-lemma : (a : ℕ) (p : rℕ(0 , a) ≡ (0 , a))
          → (pred-ℤ ∘ succ-ℤ) ((0 , a) , p) ≡ ((0 , a) , p)
  η-lemma zero p            = pair⁼ (refl (zero , zero) , isSet-ℕ×ℕ _ _)
  η-lemma (succ zero) p     = pair⁼ (refl (0 , 1) , isSet-ℕ×ℕ _ _)
  η-lemma (succ (succ a)) p = pair⁼ (refl (zero , succ (succ a)) , isSet-ℕ×ℕ _ _)

  ε : (succ-ℤ ∘ pred-ℤ) ∼ id
  ε ((zero , zero) , p)     = pair⁼ (refl (zero , zero) , isSet-ℕ×ℕ _ _)
  ε ((zero , succ b) , p)   = pair⁼ (refl (zero , succ b) , isSet-ℕ×ℕ _ _)
  ε ((succ a , zero) , p)   = ε-lemma (succ a) p
  ε ((succ a , succ b) , p) = !𝟘 _ (rℕ-¬succ a b p)

  η : (pred-ℤ ∘ succ-ℤ) ∼ id
  η ((zero , zero) , p)     = pair⁼ (refl (zero , zero) , isSet-ℕ×ℕ _ _)
  η ((zero , succ b) , p)   = η-lemma (succ b) p
  η ((succ a , zero) , p)   = pair⁼ (refl (succ a , zero) , isSet-ℕ×ℕ _ _)
  η ((succ a , succ b) , p) = !𝟘 _ (rℕ-¬succ a b p)

-- Some additional lemmas
pred-ℤ-ℕ-in-ℤ≤0 : (n : ℕ) → (pred-ℤ (ℕ-in-ℤ≤0 n)) ≡ (ℕ-in-ℤ≤0 (succ n))
pred-ℤ-ℕ-in-ℤ≤0 zero     = pair⁼(refl _ , isSet-ℕ×ℕ _ _)
pred-ℤ-ℕ-in-ℤ≤0 (succ n) = pair⁼(refl _ , isSet-ℕ×ℕ _ _)

pred-ℤ-ℕ-in-ℤ≥0 : (n : ℕ) → (pred-ℤ (ℕ-in-ℤ≥0 (succ n))) ≡ (ℕ-in-ℤ≥0 n)
pred-ℤ-ℕ-in-ℤ≥0 n = pair⁼(refl _ , isSet-ℕ×ℕ _ _)

succ-ℤ-ℕ-in-ℤ≤0 : (n : ℕ) → (succ-ℤ (ℕ-in-ℤ≤0 (succ n))) ≡ (ℕ-in-ℤ≤0 n)
succ-ℤ-ℕ-in-ℤ≤0 zero     = pair⁼(refl _ , isSet-ℕ×ℕ _ _)
succ-ℤ-ℕ-in-ℤ≤0 (succ n) = pair⁼(refl _ , isSet-ℕ×ℕ _ _)

succ-ℤ-ℕ-in-ℤ≥0 : (n : ℕ) → (succ-ℤ (ℕ-in-ℤ≥0 n)) ≡ (ℕ-in-ℤ≥0 (succ n))
succ-ℤ-ℕ-in-ℤ≥0 zero     = pair⁼(refl _ , isSet-ℕ×ℕ _ _)
succ-ℤ-ℕ-in-ℤ≥0 (succ n) = pair⁼(refl _ , isSet-ℕ×ℕ _ _)
```
