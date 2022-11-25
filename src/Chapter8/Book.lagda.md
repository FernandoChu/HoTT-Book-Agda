---
title: Chapter 8. Homotopy Theory
---

# Chapter 8. Homotopy Theory

```agda
module Chapter8.Book where

open import Chapter7.Exercises public
```

```agda
-- Definition 8.0.1.
πₙ : (n : ℕ) (A : 𝒰 𝒾) (a : A) → 𝒰 𝒾
πₙ zero A a = A
πₙ (succ n) A a = ∥ pr₁ (Ωⁿ (succ n) (A , a)) ∥₀
```

## Section 8.1 π₁(𝕊¹)
```agda
-- Helper for next definition
nConcat : (n : ℕ) {A : 𝒰 𝒾} {a : A} (p : a ≡ a) → (a ≡ a)
nConcat zero p = p
nConcat (succ n) p = nConcat n p ∙ p

-- Unnumbered definition
loop^ : ℤ → base ≡ base
loop^ = ℤ-rec (base ≡ base) (refl base) (_∙ loop) (_∙ (loop ⁻¹))

-- Some obvious consequences
loop^-0ℤ : loop^ 0ℤ ≡ refl base
loop^-0ℤ = ℤ-rec-comp-0ℤ (base ≡ base) (refl base) (_∙ loop) (_∙ (loop ⁻¹))

loop^-ℕ-in-ℤ≤0-succ : (n : ℕ)
                    → loop^ (ℕ-in-ℤ≤0 (succ n)) ≡ loop^ (ℕ-in-ℤ≤0 n) ∙ loop ⁻¹
loop^-ℕ-in-ℤ≤0-succ n =
  ℤ-rec-comp-ℤ≤0 (base ≡ base) (refl base) (_∙ loop) (_∙ (loop ⁻¹)) n

loop^-ℕ-in-ℤ≥0-succ : (n : ℕ)
                    → loop^ (ℕ-in-ℤ≥0 (succ n)) ≡ loop^ (ℕ-in-ℤ≥0 n) ∙ loop
loop^-ℕ-in-ℤ≥0-succ n =
  ℤ-rec-comp-ℤ≥0 (base ≡ base) (refl base) (_∙ loop) (_∙ (loop ⁻¹)) n

loop^-succ : (z : ℤ) → loop^ (succ-ℤ z) ≡ loop^ z ∙ loop
loop^-succ z =
  ⊎-rec _
   (λ (n , p) → begin
     loop^ (succ-ℤ z)                      ≡⟨ ap (loop^ ∘ succ-ℤ) p ⟩
     loop^ (succ-ℤ (ℕ-in-ℤ≤0 (succ n)))    ≡⟨ ap loop^ (succ-ℤ-ℕ-in-ℤ≤0 n) ⟩
     loop^ (ℕ-in-ℤ≤0 n)                    ≡˘⟨ refl-right ⟩
     loop^ (ℕ-in-ℤ≤0 n) ∙ refl base        ≡˘⟨ ap (loop^ (ℕ-in-ℤ≤0 n) ∙_) (⁻¹-left∙ loop) ⟩
     loop^ (ℕ-in-ℤ≤0 n) ∙ (loop ⁻¹ ∙ loop) ≡˘⟨ ∙-assoc (loop^ (ℕ-in-ℤ≤0 n)) ⟩
     loop^ (ℕ-in-ℤ≤0 n) ∙ loop ⁻¹ ∙ loop   ≡˘⟨ ap (_∙ loop) (loop^-ℕ-in-ℤ≤0-succ n) ⟩
     loop^ (ℕ-in-ℤ≤0 (succ n)) ∙ loop      ≡˘⟨ ap (λ - → loop^ - ∙ loop) p ⟩
     loop^ z ∙ loop                        ∎)
   (λ (n , p) → begin
     loop^ (succ-ℤ z)            ≡⟨ ap (loop^ ∘ succ-ℤ) p ⟩
     loop^ (succ-ℤ (ℕ-in-ℤ≥0 n)) ≡⟨ ap loop^ (succ-ℤ-ℕ-in-ℤ≥0 n) ⟩
     loop^ (ℕ-in-ℤ≥0 (succ n))   ≡⟨ loop^-ℕ-in-ℤ≥0-succ n ⟩
     loop^ (ℕ-in-ℤ≥0 n) ∙ loop   ≡˘⟨ ap (λ - → loop^ - ∙ loop) p ⟩
     loop^ z ∙ loop              ∎)
   (ℤ-<0∨≥0 z)

loop^-pred : (z : ℤ) → loop^ (pred-ℤ z) ≡ loop^ z ∙ (loop ⁻¹)
loop^-pred z =
  ⊎-rec _
   (λ (n , p) → begin
     loop^ (pred-ℤ z)             ≡⟨ ap (loop^ ∘ pred-ℤ) p ⟩
     loop^ (pred-ℤ (ℕ-in-ℤ≤0 n))  ≡⟨ ap loop^ (pred-ℤ-ℕ-in-ℤ≤0 n) ⟩
     loop^ (ℕ-in-ℤ≤0 (succ n))    ≡⟨ loop^-ℕ-in-ℤ≤0-succ n ⟩
     loop^ (ℕ-in-ℤ≤0 n) ∙ loop ⁻¹ ≡˘⟨ ap (λ - → loop^ - ∙ loop ⁻¹) p ⟩
     loop^ z ∙ loop ⁻¹ ∎)
   (λ (n , p) → begin
     loop^ (pred-ℤ z)                      ≡⟨ ap (loop^ ∘ pred-ℤ) p ⟩
     loop^ (pred-ℤ (ℕ-in-ℤ≥0 (succ n)))    ≡⟨ ap loop^ (pred-ℤ-ℕ-in-ℤ≥0 n) ⟩
     loop^ (ℕ-in-ℤ≥0 n)                    ≡˘⟨ refl-right ⟩
     loop^ (ℕ-in-ℤ≥0 n) ∙ refl base        ≡˘⟨ ap (loop^ (ℕ-in-ℤ≥0 n) ∙_) (⁻¹-right∙ loop) ⟩
     loop^ (ℕ-in-ℤ≥0 n) ∙ (loop ∙ loop ⁻¹) ≡˘⟨ ∙-assoc (loop^ (ℕ-in-ℤ≥0 n)) ⟩
     loop^ (ℕ-in-ℤ≥0 n) ∙ loop ∙ loop ⁻¹   ≡˘⟨ ap (_∙ loop ⁻¹) (loop^-ℕ-in-ℤ≥0-succ n) ⟩
     loop^ (ℕ-in-ℤ≥0 (succ n)) ∙ loop ⁻¹   ≡˘⟨ ap (λ - → loop^ - ∙ loop ⁻¹) p ⟩
     loop^ z ∙ loop ⁻¹ ∎)
   (ℤ-≤0∨>0 z)

-- Definition 8.1.1.
code-𝕊¹ : 𝕊¹ → 𝒰₀
code-𝕊¹ = 𝕊¹-rec 𝒰₀ ℤ (ua succ-ℤ-≃)

-- Lemma 8.1.2.
tr-code-𝕊¹-loop : (x : ℤ) → tr code-𝕊¹ loop x ≡ succ-ℤ x
tr-code-𝕊¹-loop x = begin
  tr code-𝕊¹ loop x                 ≡⟨⟩
  tr (id ∘ code-𝕊¹) loop x          ≡⟨  happly (tr-ap-assoc code-𝕊¹ loop) x  ⟩
  tr (λ x → x) (ap code-𝕊¹ loop) x  ≡⟨ ap (λ - → tr id - x) (𝕊¹-rec-comp _ _ _) ⟩
  tr (λ x → x) (ua succ-ℤ-≃) x      ≡⟨⟩
  pr₁ (idtoeqv (ua succ-ℤ-≃)) x     ≡⟨ ≡-𝒰-comp succ-ℤ-≃ x ⟩
  succ-ℤ x                    ∎

tr-code-𝕊¹-loop⁻¹ : (x : ℤ) → tr code-𝕊¹ (loop ⁻¹) x ≡ pred-ℤ x
tr-code-𝕊¹-loop⁻¹ x = begin
  tr code-𝕊¹ (loop ⁻¹) x                 ≡⟨⟩
  tr (id ∘ code-𝕊¹) (loop ⁻¹) x          ≡⟨ happly (tr-ap-assoc code-𝕊¹ (loop ⁻¹)) x  ⟩
  tr (λ x → x) (ap code-𝕊¹ (loop ⁻¹)) x  ≡˘⟨ ap (λ - → tr id - x) (ap-⁻¹ code-𝕊¹ loop) ⟩
  tr (λ x → x) ((ap code-𝕊¹ loop )⁻¹) x  ≡⟨ ap (λ - → tr id (- ⁻¹) x) (𝕊¹-rec-comp _ _ _) ⟩
  tr (λ x → x) ((ua succ-ℤ-≃)⁻¹) x       ≡⟨ ap (λ - → tr id - x) (ua⁻¹ succ-ℤ-≃) ⟩
  tr (λ x → x) (ua (≃-sym succ-ℤ-≃)) x   ≡⟨ ≡-𝒰-comp (≃-sym succ-ℤ-≃) x ⟩
  pred-ℤ x                    ∎

-- Definition 8.1.5.
encode-𝕊¹ : (x : 𝕊¹) → (base ≡ x) → code-𝕊¹ x
encode-𝕊¹ x p = tr code-𝕊¹ p 0ℤ

-- Definition 8.1.6.
decode-𝕊¹ : (x : 𝕊¹) → code-𝕊¹ x → (base ≡ x)
decode-𝕊¹ = 𝕊¹-ind (λ x → code-𝕊¹ x → base ≡ x) loop^ ≡tr
 where
  ≡tr : tr (λ x → code-𝕊¹ x → base ≡ x) loop loop^ ≡ loop^
  ≡tr = begin
    tr (λ x → code-𝕊¹ x → base ≡ x) loop loop^       ≡⟨ i ⟩
    tr (base ≡_) loop ∘ loop^ ∘ tr code-𝕊¹ (loop ⁻¹) ≡⟨ ii ⟩
    (_∙ loop) ∘ loop^ ∘ tr code-𝕊¹ (loop ⁻¹)         ≡⟨ iii ⟩
    (_∙ loop) ∘ loop^ ∘ pred-ℤ                       ≡⟨⟩
    (λ n → loop^ (pred-ℤ n) ∙ loop)                  ≡⟨ iv ⟩

    (λ n → loop^ n ∙ loop ⁻¹ ∙ loop)                 ≡⟨ v ⟩
    (λ n → loop^ n ∙ (loop ⁻¹ ∙ loop))               ≡⟨ vi ⟩
    (λ n → loop^ n ∙ refl base)                      ≡⟨ vii ⟩
    loop^ ∎
   where
    i   = funext (λ - → happly (tr-→ loop loop^) -)
    ii  = ap (_∘ (loop^ ∘ tr code-𝕊¹ (loop ⁻¹)))
             (funext (λ - → tr-Homc─ base loop -))
    iii = ap ((_∙ loop) ∘ loop^ ∘_) (funext tr-code-𝕊¹-loop⁻¹)
    iv = funext (λ n → ap (_∙ loop) (loop^-pred n))
    v = funext (λ n → ∙-assoc (loop^ n))
    vi = funext (λ n → ap (loop^ n ∙_) (⁻¹-left∙ loop))
    vii = funext (λ n → refl-right)

-- Lemma 8.1.7.
decode∘encode-𝕊¹∼id : (x : 𝕊¹) → (p : base ≡ x)
                    → decode-𝕊¹ x (encode-𝕊¹ x p) ≡ p
decode∘encode-𝕊¹∼id x (refl x) = loop^-0ℤ

-- Lemma 8.1.7.
encode∘decode-𝕊¹∼id : (x : 𝕊¹) → (c : code-𝕊¹ x)
                    → encode-𝕊¹ x (decode-𝕊¹ x c) ≡ c
encode∘decode-𝕊¹∼id = 𝕊¹-ind _
 (ℤ-ind _ (ap (encode-𝕊¹ base) loop^-0ℤ)
  (λ n p → begin
    encode-𝕊¹ base (loop^ (ℕ-in-ℤ≥0 (succ n)))   ≡⟨ ap (encode-𝕊¹ base)
                                                       (loop^-ℕ-in-ℤ≥0-succ n) ⟩
    encode-𝕊¹ base (loop^ (ℕ-in-ℤ≥0 n) ∙ loop)   ≡⟨⟩
    tr code-𝕊¹ (loop^ (ℕ-in-ℤ≥0 n) ∙ loop) 0ℤ    ≡˘⟨ happly (tr-∘ code-𝕊¹ (loop^
                                                      (ℕ-in-ℤ≥0 n)) loop) 0ℤ ⟩
    tr code-𝕊¹ loop (tr code-𝕊¹
      (loop^ (ℕ-in-ℤ≥0 n)) 0ℤ)                   ≡⟨ tr-code-𝕊¹-loop _ ⟩
    succ-ℤ (tr code-𝕊¹ (loop^ (ℕ-in-ℤ≥0 n)) 0ℤ)  ≡⟨ ap succ-ℤ p ⟩
    succ-ℤ (ℕ-in-ℤ≥0 n)                          ≡⟨ succ-ℤ-ℕ-in-ℤ≥0 n ⟩
    ℕ-in-ℤ≥0 (succ n)                            ∎)
  (λ n p → begin
    encode-𝕊¹ base (loop^ (ℕ-in-ℤ≤0 (succ n)))     ≡⟨ ap (encode-𝕊¹ base)
                                                         (loop^-ℕ-in-ℤ≤0-succ n) ⟩
    encode-𝕊¹ base (loop^ (ℕ-in-ℤ≤0 n) ∙ loop ⁻¹)  ≡⟨⟩
    tr code-𝕊¹ (loop^ (ℕ-in-ℤ≤0 n) ∙ loop ⁻¹) 0ℤ   ≡˘⟨ happly (tr-∘ code-𝕊¹ (loop^
                                                        (ℕ-in-ℤ≤0 n)) (loop ⁻¹)) 0ℤ ⟩
    tr code-𝕊¹ (loop ⁻¹) (tr code-𝕊¹
      (loop^ (ℕ-in-ℤ≤0 n)) 0ℤ)                     ≡⟨ tr-code-𝕊¹-loop⁻¹ _ ⟩
    pred-ℤ (tr code-𝕊¹ (loop^ (ℕ-in-ℤ≤0 n)) 0ℤ)    ≡⟨ ap pred-ℤ p ⟩
    pred-ℤ (ℕ-in-ℤ≤0 n)                            ≡⟨ pred-ℤ-ℕ-in-ℤ≤0 n ⟩
    ℕ-in-ℤ≤0 (succ n) ∎))
 (funext (λ n → isSet-ℤ _ _))

-- Theorem 8.1.9.
code-𝕊¹-≃ : (x : 𝕊¹) → (base ≡ x) ≃ (code-𝕊¹ x)
code-𝕊¹-≃ x =
  encode-𝕊¹ x , invs⇒equivs (encode-𝕊¹ x)
    (decode-𝕊¹ x , encode∘decode-𝕊¹∼id x , decode∘encode-𝕊¹∼id x)

-- Corollary 8.1.10.
Ω𝕊¹≡ℤ : (base ≡ base) ≡ ℤ
Ω𝕊¹≡ℤ = ua (code-𝕊¹-≃ base)

-- Corollary 8.1.11.
-- π₁𝕊¹ : πₙ 1 𝕊¹ base ≡ ℤ
-- π₁𝕊¹ = _

-- πₙ𝕊¹ : (n : ℕ) → πₙ (succ (succ n)) 𝕊¹ base ≡ 𝟙
-- πₙ𝕊¹ = _

```
