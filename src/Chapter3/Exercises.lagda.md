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
isProp-implies-point→isContr : {A : 𝒰 𝒾}
    → isProp A → (A → isContr A)
isProp-implies-point→isContr fp c = (c , λ x → fp c x)

point→isContr-implies-isProp : {A : 𝒰 𝒾}
    → (A → isContr A) → isProp A
point→isContr-implies-isProp g x y =
  pr₂ (isContr⇒isPointedProp (domain g) (g x)) x y

isProp≃point→isContr : {A : 𝒰 𝒾}
    → isProp A ≃ (A → isContr A)
isProp≃point→isContr {𝒾} {A} = (isProp-implies-point→isContr ,
  invs⇒equivs isProp-implies-point→isContr
    (point→isContr-implies-isProp , ε , η))
 where
  ε : (isProp-implies-point→isContr ∘ point→isContr-implies-isProp)
        ∼ id
  ε g = funext (λ x → isProp-isContr _ _ _)
  η : (point→isContr-implies-isProp ∘ isProp-implies-point→isContr)
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
