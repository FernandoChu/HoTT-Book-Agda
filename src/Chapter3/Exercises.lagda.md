---
title: Chapter 3. Sets and logic - Exercises
---

# Chapter 3. Sets and logic - Exercises

```agda
module Chapter3.Exercises where

open import Chapter3.Book public

-- Exercise 3.3.
isSet-Σ : {A : 𝒰 𝒾}
        → {B : A → 𝒰 𝒿}
        → isSet A
        → ((x : A) → isSet (B x))
        → isSet (Σ B)
isSet-Σ f g {w} {w'} p q = begin
  p                    ≡˘⟨ ≃-η eqv p ⟩
  ≃-← eqv (≃-→ eqv p)  ≡⟨ ap (≃-← eqv) (pair⁼(f _ _ , g _ _ _)) ⟩
  ≃-← eqv (≃-→ eqv q)  ≡⟨ ≃-η eqv q ⟩
  q ∎
 where
  eqv = ≡-Σ-≃ w w'

-- Exercise 3.4.
isProp⇒isContr-endo : (A : 𝒰 𝒾) → isProp A → isContr (A → A)
isProp⇒isContr-endo A h = (id , p)
  where
    p : (g : A → A) → id ≡ g
    p g = funext (λ x → h x (g x))

isContr-endo⇒isProp : (A : 𝒰 𝒾) → isContr (A → A) → isProp A
isContr-endo⇒isProp A h x y = happly (A→A-isProp (λ _ → x) (λ _ → y)) x
  where
    A→A-isProp : isProp (A → A)
    A→A-isProp = pr₂ (isContr⇒isPointedProp (A → A) h)

-- Exercise 3.5.
isProp⇒inhab→isContr : {A : 𝒰 𝒾}
    → isProp A → (A → isContr A)
isProp⇒inhab→isContr fp c = (c , λ x → fp c x)

inhab→isContr⇒isProp : {A : 𝒰 𝒾}
    → (A → isContr A) → isProp A
inhab→isContr⇒isProp g x y =
  pr₂ (isContr⇒isPointedProp (domain g) (g x)) x y

isProp≃inhab→isContr : {A : 𝒰 𝒾}
    → isProp A ≃ (A → isContr A)
isProp≃inhab→isContr {𝒾} {A} = (isProp⇒inhab→isContr ,
  invs⇒equivs isProp⇒inhab→isContr
    (inhab→isContr⇒isProp , ε , η))
 where
  ε : (isProp⇒inhab→isContr ∘ inhab→isContr⇒isProp)
        ∼ id
  ε g = funext (λ x → isProp-isContr _ _ _)
  η : (inhab→isContr⇒isProp ∘ isProp⇒inhab→isContr)
        ∼ id
  η fp = funext (λ x → funext (λ y → isProp⇒isSet fp _ _))

-- Exercise 3.6.
isProp⇒isProp-isDecidible : (A : 𝒰 𝒾) → isProp A
                          → isProp (A ⊎ (¬ A))
isProp⇒isProp-isDecidible A f (inl x) (inl y) = ap inl (f x y)
isProp⇒isProp-isDecidible A f (inl x) (inr c) = !𝟘 (inl x ≡ inr c) (c x)
isProp⇒isProp-isDecidible A f (inr c) (inl x) = !𝟘 (inr c ≡ inl x) (c x)
isProp⇒isProp-isDecidible A f (inr c) (inr d) = ap inr p
  where
    p : c ≡ d
    p = funext (λ x → !𝟘 (c x ≡ d x) (c x))

-- Exercise 3.7.
isProp⇒isProp-isDecidible' : (A : 𝒰 𝒾) → (B : 𝒰 𝒿)
                           → isProp A → isProp B → ¬ (A × B)
                           → isProp (A ⊎ B)
isProp⇒isProp-isDecidible' A B f g c (inl a) (inl a') =
  ap inl (f a a')
isProp⇒isProp-isDecidible' A B f g c (inl a) (inr b) =
  !𝟘 (inl a ≡ inr b) (c (a , b))
isProp⇒isProp-isDecidible' A B f g c (inr b) (inl a) =
  !𝟘 (inr b ≡ inl a) (c (a , b))
isProp⇒isProp-isDecidible' A B f g c (inr b) (inr b') =
  ap inr (g b b')

-- Exercise 3.9.
LEM→Prop𝒰≃𝟚 : {𝒾 : Level} → LEM 𝒾 → (Prop𝒰 𝒾 ≃ 𝟚)
LEM→Prop𝒰≃𝟚 {𝒾} LEM-holds =
  (Prop𝒰→𝟚 , invs⇒equivs Prop𝒰→𝟚 (𝟚→Prop𝒰 , ε , η))
 where
  Prop𝒰→𝟚 : Prop𝒰 𝒾 → 𝟚
  Prop𝒰→𝟚 P = ⊎-rec 𝟚 (λ _ → ₁) (λ _ → ₀) (LEM-holds (pr₁ P) (pr₂ P))
  𝟚→Prop𝒰 : 𝟚 → Prop𝒰 𝒾
  𝟚→Prop𝒰 ₀ = (Raised 𝒾 𝟘 , isProp-Raised𝟘)
  𝟚→Prop𝒰 ₁ = (Raised 𝒾 𝟙 , isProp-Raised𝟙)
  ε : (Prop𝒰→𝟚 ∘ 𝟚→Prop𝒰) ∼ id
  ε ₀ = ⊎-ind (λ - → ((⊎-rec 𝟚 (λ _ → ₁) (λ _ → ₀) -) ≡ id ₀))
    (λ {(raise ())}) (λ _ → refl ₀)
    (LEM-holds (Raised 𝒾 𝟘) isProp-Raised𝟘)
  ε ₁ = ⊎-ind (λ - → ((⊎-rec 𝟚 (λ _ → ₁) (λ _ → ₀) -) ≡ id ₁))
    (λ _ → refl ₁) (λ p → !𝟘 (₀ ≡ ₁) (p (raise ⋆)))
    (LEM-holds (Raised 𝒾 𝟙) isProp-Raised𝟙)
  η : (𝟚→Prop𝒰 ∘ Prop𝒰→𝟚) ∼ id
  η P = ⊎-ind (λ - → (𝟚→Prop𝒰 (⊎-rec 𝟚 (λ _ → ₁) (λ _ → ₀) -) ≡ P))
    (λ p → pair⁼
      (ua (isProp-areLogEq⇒Eq (Raised 𝒾 𝟙) (pr₁ P) isProp-Raised𝟙 (pr₂ P)
        (λ _ → p) (λ _ → raise ⋆))
      , isProp-isProp (pr₁ P) _ _))
    (λ ¬p → pair⁼
      (ua (isProp-areLogEq⇒Eq (Raised 𝒾 𝟘) (pr₁ P) isProp-Raised𝟘 (pr₂ P)
        (λ {(raise ())}) (λ p → !𝟘 _ (¬p p)))
      , isProp-isProp (pr₁ P) _ _))
    (LEM-holds (pr₁ P) (pr₂ P))

Prop𝒰≃𝟚→LEM : {𝒾 : Level} → (Prop𝒰 𝒾 ≃ 𝟚) → LEM 𝒾
Prop𝒰≃𝟚→LEM {𝒾} Prop𝒰𝒾≃𝟚 P isProp-P =
 ⊎-rec (P ⊎ ¬ P)
   -- imP ≡ ₀
   (λ p → ⊎-rec _
     -- (im𝟘 ≡ ₀) × (im𝟙 ≡ ₁)
     (λ (q , r) → inr (λ P-holds → !𝟘' _
       (tr id (ap pr₁ (≃-→-cancel Prop𝒰𝒾≃𝟚 (p ∙ (q ⁻¹)))) P-holds)))
     -- (im𝟘 ≡ ₁) × (im𝟙 ≡ ₀)
     (λ (q , r) → inl
       (tr id (ap pr₁ (≃-→-cancel Prop𝒰𝒾≃𝟚 (r ∙ (p ⁻¹)))) (raise ⋆)))
     H)
   -- imP ≡ ₁
   (λ p → ⊎-rec _
     -- (im𝟘 ≡ ₀) × (im𝟙 ≡ ₁)
     (λ (q , r) → inl
       (tr id (ap pr₁ (≃-→-cancel Prop𝒰𝒾≃𝟚 (r ∙ (p ⁻¹)))) (raise ⋆)))
     -- (im𝟘 ≡ ₁) × (im𝟙 ≡ ₀)
     (λ (q , r) → inr (λ P-holds → !𝟘' _
       (tr id (ap pr₁ (≃-→-cancel Prop𝒰𝒾≃𝟚 (p ∙ (q ⁻¹)))) P-holds)))
     H)
   (₀or₁ imP)
 where
  !𝟘' : (C : 𝒰 𝒿) → Raised 𝒾 𝟘 → C
  !𝟘' C (raise ())
  ₀or₁ : (x : 𝟚) → (x ≡ ₀) ⊎ (x ≡ ₁)
  ₀or₁ ₀ = inl (refl ₀)
  ₀or₁ ₁ = inr (refl ₁)
  imP im𝟘 im𝟙 : 𝟚
  imP = ≃-→ Prop𝒰𝒾≃𝟚 (P , isProp-P)
  im𝟘 = ≃-→ Prop𝒰𝒾≃𝟚 (Raised 𝒾 𝟘 , isProp-Raised𝟘)
  im𝟙 = ≃-→ Prop𝒰𝒾≃𝟚 (Raised 𝒾 𝟙 , isProp-Raised𝟙)
  H : ((im𝟘 ≡ ₀) × (im𝟙 ≡ ₁)) ⊎ ((im𝟘 ≡ ₁) × (im𝟙 ≡ ₀))
  H = ⊎-rec ((im𝟘 ≡ ₀) × (im𝟙 ≡ ₁) ⊎ (im𝟘 ≡ ₁) × (im𝟙 ≡ ₀))
    -- im𝟘 ≡ ₀
    (⊎-rec _
      -- im𝟙 ≡ ₀
      (λ p q → !𝟘' _ (absurd (q ∙ (p ⁻¹))))
      -- im𝟙 ≡ ₁
      (λ p q → inr (p , q))
      (₀or₁ im𝟘))
    -- im𝟘 ≡ ₁
    (⊎-rec _
      -- im𝟙 ≡ ₀
      (λ p q → inl (p , q))
      -- im𝟙 ≡ ₁
      (λ p q → !𝟘' _ (absurd (q ∙ (p ⁻¹))))
      (₀or₁ im𝟘))
    (₀or₁ im𝟙)
   where
     absurd : (im𝟙 ≡ im𝟘) → Raised 𝒾 𝟘
     absurd p = tr id  (ap pr₁ (≃-→-cancel Prop𝒰𝒾≃𝟚 p)) (raise ⋆)

-- Exercise 3.18.
LEM→RAA : {𝒾 : Level} → LEM 𝒾 → RAA 𝒾
LEM→RAA f A isProp-A nnA = lemma (f A isProp-A)
  where
    lemma : A ⊎ ¬ A → A
    lemma (inl x) = x
    lemma (inr x) = !𝟘 A (nnA x)

RAA→LEM : {𝒾 : Level} → RAA 𝒾 → LEM 𝒾
RAA→LEM f A isProp-A =
  f (A ⊎ ¬ A)
    (isProp⇒isProp-isDecidible A isProp-A)
    (λ g → g (inr (λ a → g (inl a))))

-- Exercise 3.20.
isContr-Σ⇒fiber-base : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿)
                     → ((a , f) : isContr A)
                     → (Σ x ꞉ A , P x) ≃ P a
isContr-Σ⇒fiber-base {𝒾} {𝒿} {A} P (a , f) =
  map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  isSet-A : isSet A
  isSet-A = isProp⇒isSet (pr₂ (isContr⇒isPointedProp A (a , f)))
  map = λ (x , px) → tr P ((f x)⁻¹) px
  map⁻¹ = λ pa → (a , pa)
  ε = λ pa → ap (λ - → tr P - pa) (isSet-A ((f a)⁻¹) (refl a))
  η : (map⁻¹ ∘ map) ∼ id
  η (x , px) = pair⁼ (f x , s)
   where
    s : tr P (f x) (tr P ((f x)⁻¹) px) ≡ px
    s = begin
     tr P (f x) (tr P ((f x)⁻¹) px) ≡⟨ happly (tr-∘ P ((f x)⁻¹) (f x)) px ⟩
     tr P ((f x)⁻¹ ∙ (f x)) px      ≡⟨ ap (λ - → tr P - px)
                                          (isSet-A ((f x)⁻¹ ∙ (f x)) (refl x)) ⟩
     px                             ∎
```
