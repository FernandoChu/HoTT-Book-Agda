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
-- 𝕊¹→-≃ : {A : 𝒰 𝒾}
--       → is-univalent 𝒾
--       → has-funext lzero 𝒾
--       → has-funext 𝒾 𝒾
--       → has-funext 𝒾 (𝒾 ⁺)
--       → (𝕊¹ → A) ≃ (Σ x ꞉ A , x ≡ x)
-- 𝕊¹→-≃ {𝒾} {A} u fe1 fe2 fe3 =
--   φ , ishae→biinv φ (contrMap→hae u fe2 fe3 φ contrFib)
--  where
--   φ : (𝕊¹ → A) → (Σ x ꞉ A , x ≡ x)
--   φ g = g base , ap g loop

--   contrFib : (y : codomain φ) → isContr (fib φ y)
--   contrFib y@(b , l) = pointed-props-are-contr (fib φ y) (fibφ , fibeq)
--    where
--     f' = 𝕊¹-rec A b l
--     eqf' = pair⁼(refl b , 𝕊¹-rec-comp A b l)
--     fibφ = (f' , eqf')

--     fibeq : ((f , eqf) (g , eqg) : fib φ (b , l)) → (f , eqf) ≡ (g , eqg)
--     fibeq (f , eqf) (g , eqg) = pair⁼(f≡g , eqf≡eqg)
--      where
--       f≡g-lemma : tr (λ x → x ≡ x) (ap pr₁ eqf ∙ (ap pr₁ eqg)⁻¹)
--                     (ap f loop) ≡ ap g loop
--       f≡g-lemma = begin
--         tr (λ x → x ≡ x) (ap pr₁ eqf ∙ (ap pr₁ eqg)⁻¹) (ap f loop) ≡˘⟨ i ⟩
--         tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
--           (tr (λ x → x ≡ x) (ap pr₁ eqf) (ap f loop))              ≡˘⟨ ii ⟩
--         tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
--           (tr (λ x → x ≡ x) (pr₁ (pair⁼⁻¹ eqf)) (ap f loop))       ≡⟨ iii ⟩
--         tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) l ≡⟨ iv ⟩
--         tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
--           (tr (λ x → x ≡ x) (pr₁ (pair⁼⁻¹ eqg)) (ap g loop))       ≡⟨ v ⟩
--         tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
--           (tr (λ x → x ≡ x) (ap pr₁ eqg) (ap g loop))              ≡⟨ vi ⟩
--         tr (λ x → x ≡ x) (ap pr₁ eqg ∙ (ap pr₁ eqg)⁻¹) (ap g loop) ≡⟨ vii ⟩
--         ap g loop ∎
--        where
--         i = happly (tr-∘ (λ x → x ≡ x) (ap pr₁ eqf) ((ap pr₁ eqg)⁻¹)) (ap f loop)
--         ii = ap (λ - → tr (λ x → x ≡ x)
--                ((ap pr₁ eqg)⁻¹) (tr (λ x → x ≡ x) - (ap f loop)))
--                (pr₁pair⁼⁻¹-is-ap eqf)
--         iii = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) -) (pr₂ (pair⁼⁻¹ eqf))
--         iv = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) -)
--                  ((pr₂ (pair⁼⁻¹ eqg))⁻¹)
--         v = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
--                   (tr (λ x → x ≡ x) - (ap g loop))) (pr₁pair⁼⁻¹-is-ap eqg)
--         vi = happly (tr-∘ (λ x → x ≡ x) (ap pr₁ eqg) ((ap pr₁ eqg)⁻¹))
--                      (ap g loop)
--         vii = ap (λ - → tr (λ x → x ≡ x) - (ap g loop)) (⁻¹-right∙ (ap pr₁ eqg))

--       f≡g = funext fe1
--               (𝕊¹-ind-uniq f g ((ap pr₁ eqf ∙ (ap pr₁ eqg)⁻¹)) f≡g-lemma)

--       eqf≡eqg : tr (λ x → φ x ≡ b , l) f≡g eqf ≡ eqg
--       eqf≡eqg = begin
--         tr (λ x → φ x ≡ b , l) f≡g eqf              ≡⟨ i ⟩
--         (ap φ f≡g)⁻¹ ∙ eqf ∙ (ap (λ _ → b , l) f≡g) ≡⟨ ii ⟩
--         (ap φ f≡g)⁻¹ ∙ eqf ∙ refl _                 ≡⟨ iii ⟩
--         (ap φ f≡g)⁻¹ ∙ (eqf ∙ refl _)               ≡⟨ iv ⟩
--         (ap φ f≡g)⁻¹ ∙ eqf                          ≡⟨ v eqf eqg ⟩
--         eqg ∎
--        where
--         i = tr-fx≡gx φ (λ _ → (b , l)) f≡g eqf
--         ii = ap ((ap φ f≡g)⁻¹ ∙ eqf ∙_) (ap-const f≡g (b , l))
--         iii = ∙-assoc ((ap φ f≡g)⁻¹)
--         iv = ap ((ap φ f≡g)⁻¹ ∙_) refl-right
--         v : (eqf : φ f ≡ b , l) (eqg : φ g ≡ b , l) → (ap φ f≡g)⁻¹ ∙ eqf ≡ eqg
--         v (refl _) eqg = refl-right ∙ arst
--           where
--             arst : (ap φ (funext fe1 _))⁻¹ ≡ eqg
--             arst = _
--         v' : (eqf : φ f ≡ b , l) (eqg : φ g ≡ b , l) → (ap φ f≡g)⁻¹ ∙ eqf ≡ eqg
--         v' eqf eqg = arst
--           where
--             arst : {!ap φ f≡g ⁻¹ ∙ eqf ≡ eqg!}
--             arst = _
        -- v (refl _) eqg (refl h) = refl-left ∙ {!!}

    -- fibeq : ((g , eqg) : fib φ (b , l)) → (f , eqf) ≡ (g , eqg)
    -- fibeq (g , eqg) = pair⁼(f≡g , eqf≡eqg)
    --  where
    --   f≡g-lemma : tr (λ x → x ≡ x) (ap pr₁ eqg ⁻¹) (ap f loop) ≡ ap g loop
    --   f≡g-lemma = begin
    --     tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) (ap f loop)              ≡⟨ i ⟩
    --     tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) l                        ≡⟨ ii ⟩
    --     tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
    --       (tr (λ x → x ≡ x) (pr₁ (pair⁼⁻¹ eqg)) (ap g loop))       ≡⟨ iii ⟩
    --     tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
    --       (tr (λ x → x ≡ x) (ap pr₁ eqg) (ap g loop))              ≡⟨ iv ⟩
    --     tr (λ x → x ≡ x) (ap pr₁ eqg ∙ (ap pr₁ eqg)⁻¹) (ap g loop) ≡⟨ v ⟩
    --     ap g loop ∎
    --    where
    --     i = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) -) (𝕊¹-rec-comp A b l)
    --     ii = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) -)
    --              ((pr₂ (pair⁼⁻¹ eqg))⁻¹)
    --     Σ-lemma : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {w₁ w₂ : Σ B} (p : w₁ ≡ w₂)
    --             → pr₁ (pair⁼⁻¹ p) ≡ ap pr₁ p
    --     Σ-lemma (refl _) = refl _
    --     iii = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
    --               (tr (λ x → x ≡ x) - (ap g loop))) (Σ-lemma eqg)
    --     iv = happly (tr-∘ (λ x → x ≡ x) (ap pr₁ eqg) ((ap pr₁ eqg)⁻¹))
    --                  (ap g loop)
    --     v = ap (λ - → tr (λ x → x ≡ x) - (ap g loop)) (⁻¹-right∙ (ap pr₁ eqg))
    --   f≡g = funext fe1 (𝕊¹-ind-uniq f g ((ap pr₁ eqg)⁻¹) f≡g-lemma)
    --   eqf≡eqg : tr (λ x → φ x ≡ b , l) f≡g eqf ≡ eqg
    --   eqf≡eqg = begin
    --     tr (λ x → φ x ≡ b , l) f≡g eqf              ≡⟨ i ⟩
    --     (ap φ f≡g)⁻¹ ∙ eqf ∙ (ap (λ _ → b , l) f≡g) ≡⟨ ii ⟩
    --     (ap φ f≡g)⁻¹ ∙ eqf ∙ refl _                 ≡⟨ iii ⟩
    --     (ap φ f≡g)⁻¹ ∙ (eqf ∙ refl _)               ≡⟨ iv ⟩
    --     (ap φ f≡g)⁻¹ ∙ eqf                          ≡⟨ v eqf eqg f≡g ⟩
    --     eqg ∎
    --    where
    --     i = tr-fx≡gx φ (λ _ → (b , l)) f≡g eqf
    --     ii = ap ((ap φ f≡g)⁻¹ ∙ eqf ∙_) (ap-const f≡g (b , l))
    --     iii = ∙-assoc ((ap φ f≡g)⁻¹)
    --     iv = ap ((ap φ f≡g)⁻¹ ∙_) refl-right
    --     v : {f g : 𝕊¹ → A} (eqf : φ f ≡ b , l) (eqg : φ g ≡ b , l) (p : f ≡ g) → (ap φ p)⁻¹ ∙ eqf ≡ eqg
    --     v (refl _) eqg (refl h) = refl-left ∙ _
```

## 6.3 The interval

```agda
𝕀-isContr : isContr 𝕀
𝕀-isContr = (1ᵢ , λ x → (contr x)⁻¹)
 where
  contr : (x : 𝕀) → (x ≡ 1ᵢ)
  contr = 𝕀-ind (λ x → x ≡ 1ᵢ) seg (refl 1ᵢ) treq
   where
    treq : tr (λ x → x ≡ 1ᵢ) seg seg ≡ refl 1ᵢ
    treq = (trHom-c 1ᵢ seg seg) ∙ (⁻¹-left∙ seg)
```

## 6.4 Circles and spheres

```agda
-- Lemma 6.4.1.
loop≢refl : (is-univalent lzero)
          → loop ≢ refl base
loop≢refl u eq = 𝒰₀-is-not-set u (A-is-set 𝒰₀)
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


𝝨𝟚≃𝕊¹ : 𝝨 𝟚 ≃ 𝕊¹
𝝨𝟚≃𝕊¹ = f , invs-are-equivs f (g , ε , η)
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
      VIII = ap (λ - → (loop ∙ -)⁻¹ ∙ loop) (ap⁻¹ f (merid 𝟚 ₁))⁻¹
      IX   = ap (λ - → (loop ∙ (-)⁻¹)⁻¹ ∙ loop)
                 (𝝨-rec-comp 𝟚 𝕊¹ base base
                  (𝟚-rec (base ≡ base) loop (refl base)) ₁)
      X    = ap (λ - → (-)⁻¹ ∙ loop) refl-right
      XI   = ⁻¹-left∙ loop

Map* : ((A , a₀) : 𝒰∙ 𝒾) → ((B , b₀) : 𝒰∙ 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
Map* (A , a₀) (B , b₀) = Σ f ꞉ (A → B) , f a₀ ≡ b₀

_₊ : (A : 𝒰 𝒾) → 𝒰∙ 𝒾
A ₊ = (A ⊎ 𝟙) , inr ⋆

-- Lemma 6.5.3.
Map₊≃ : has-funext 𝒾 𝒿
      → (A : 𝒰 𝒾) → ((B , b₀) : 𝒰∙ 𝒿)
      → Map* (A ₊) (B , b₀) ≃ (A → B)
Map₊≃ fe A (B , b₀) = map , invs-are-equivs map (map⁻¹ , ε , η)
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
    f'≡f = funext fe f'∼f

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
      v   = ap (λ - → (- (inr ⋆))⁻¹) (≡fe-comp fe f'∼f)
      vi  = ⁻¹-involutive eq
```

## 6.9 Truncations

```agda
module 0-Truncations where
  private
    data PT (A : 𝒰 𝒾) : 𝒰 𝒾 where
      forget : A → PT A

  ∥_∥₀ : {𝒾 : Level} → (A : 𝒰 𝒾) → 𝒰 𝒾
  ∥ A ∥₀ = PT A

  ∣_∣₀ : {𝒾 : Level} → {A : 𝒰 𝒾} → A → ∥ A ∥₀
  ∣ a ∣₀ = forget a

  postulate ∥∥₀-isSet : {X : 𝒰 𝒾} → isSet ∥ X ∥₀

  ∥∥₀-ind : (A : 𝒰 𝒾) (B : ∥ A ∥₀ → 𝒰 𝒿)
          → ((x y : ∥ A ∥₀) (z : B x) (w : B y)
             (p q : x ≡ y) (r : tr B p z ≡ w) (s : tr B q z ≡ w)
             → r ≡ tr² B (∥∥₀-isSet p q) z ∙ s)
          → (g : (a : A) → B (∣ a ∣₀))
          → ((x : ∥ A ∥₀) → B x)
  ∥∥₀-ind A B Bsetish g (forget x) = g x

  postulate ∥∥₀-ind-comp : (A : 𝒰 𝒾) (B : ∥ A ∥₀ → 𝒰 𝒿)
              → (Bsetish : (x y : ∥ A ∥₀) (z : B x) (w : B y)
                 (p q : x ≡ y) (r : tr B p z ≡ w) (s : tr B q z ≡ w)
                 → r ≡ tr² B (∥∥₀-isSet p q) z ∙ s)
              → (g : (a : A) → B (∣ a ∣₀))
              → (x y : ∥ A ∥₀) (z : B x) (w : B y)
                 (p q : x ≡ y)
              → apd² (∥∥₀-ind A B Bsetish g) (∥∥₀-isSet p q) ≡ Bsetish x y
                 ((∥∥₀-ind A B Bsetish g) x) ((∥∥₀-ind A B Bsetish g) y) p q
                  (apd (∥∥₀-ind A B Bsetish g) p) (apd (∥∥₀-ind A B Bsetish g) q)

-- open 0-Truncations public
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

module SetQuotient where
  private
    data Q (A : 𝒰 𝒾) (R : mereRelation A 𝒿) : 𝒰 (𝒾 ⊔ (𝒿 ⁺)) where
      proj : (a : A) → Q A R

  _∕_ : (A : 𝒰 𝒾) (R : mereRelation A 𝒿) → 𝒰 (𝒾 ⊔ (𝒿 ⁺))
  A ∕ R = Q A R
  infixr 30 _∕_

  quot : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
       → A → (A ∕ R)
  quot A R a = proj a

  postulate quot≡ : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
                  → (a b : A) → (pr₁ (R (a , b)))
                  → (quot A R a ≡ quot A R b)

  postulate ∕-isSet : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
                    → (x y : A ∕ R) (r s : x ≡ y)
                    → r ≡ s

  ∕-rec : (A : 𝒰 𝒾) (R : mereRelation A 𝒿) (B : 𝒰 𝓀)
        → (f : A → B)
        → ((a b : A) → (pr₁ (R (a , b))) → f a ≡ f b)
        → A ∕ R → B
  ∕-rec A R B f _ (proj x) = f x

  ∕-ind : (A : 𝒰 𝒾) (R : mereRelation A 𝒿) (B : A ∕ R → 𝒰 𝓀)
        → (f : (a : A) → B (quot A R a))
        → ((a b : A) → (resp : pr₁ (R (a , b)))
           → tr B (quot≡ A R a b resp) (f a) ≡ f b)
        → ((x : A ∕ R) → B x)
  ∕-ind A R B f _ (proj x) = f x

open SetQuotient public

-- Lemma 6.10.2.
quot-isSurjec : (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
               → isSurjec (quot A R)
quot-isSurjec A R = ∕-ind A R (λ z → ∥ fib (quot A R) z ∥) f f-respects-R
  where
    f : (a : A) → ∥ fib (quot A R) (quot A R a) ∥
    f a = ∣ a , refl (quot A R a) ∣
    f-respects-R : (a b : A) → (resp : pr₁ (R (a , b)))
                 → tr (λ z → ∥ fib (λ a₁ → quot A R a₁) z ∥)
                       (quot≡ A R a b resp) (f a) ≡ f b
    f-respects-R a b resp = ∥∥-isProp _ _

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

-- Definition 6.10.4.
_⃫_ : {𝒾 𝒿 𝓀 : Level}
      (A : 𝒰 𝒾) (R : mereRelation A 𝒿)
    → 𝒰 (𝒾 ⊔ 𝒿 ⊔ (𝓀 ⁺))
(_⃫_) {𝒾} {𝒿} {𝓀} A R = Σ P ꞉ (A → Prop𝒰 𝓀) , P isEquivalenceClassOf R


-- Definitions and lemmas for definition of ℤ
data _≤_ : ℕ → ℕ → 𝒰₀ where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → succ m ≤ succ n
infix 4 _≤_

¬s≤z : ∀ {m : ℕ} → ¬ (succ m ≤ zero)
¬s≤z ()
¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (succ m ≤ succ n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

≤-isDecidable : (n m : ℕ) → isDecidable (n ≤ m)
≤-isDecidable zero m = inl z≤n
≤-isDecidable (succ n) zero = inr ¬s≤z
≤-isDecidable (succ n) (succ m) =
  ⊎-rec (isDecidable (succ n ≤ succ m))
    (λ - → inl (s≤s -))
    (λ - → inr (¬s≤s -))
    (≤-isDecidable n m)

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
    (≤-isDecidable b a)

ℤ : 𝒰₀
ℤ = Σ x ꞉ (ℕ × ℕ) , (rℕ x ≡ x)
```
