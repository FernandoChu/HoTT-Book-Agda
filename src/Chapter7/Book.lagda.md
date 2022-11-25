---
title: Chapter 7. Homotopy n-types
---

# Chapter 7. Homotopy n-types

```agda
{-# OPTIONS --experimental-lossy-unification #-}

module Chapter7.Book where

open import Chapter6.Exercises public
```

## 7.1. Definition of n-types

```agda
-- Definition 7.1.1.
-- Note that this is really the property of being an n-2 type.
isNType : (n : ℕ) (A : 𝒰 𝒾) → 𝒰 𝒾
isNType 0 A        = isContr A
isNType (succ n) A = (x y : A) → isNType n (x ≡ y)

-- Example 7.1.3.
is-1Type⇒isProp : {X : 𝒰 𝒾} → isNType 1 X → isProp X
is-1Type⇒isProp f = isContr-≡⇒isProp f

isProp⇒is-1Type : {X : 𝒰 𝒾} → isProp X → isNType 1 X
isProp⇒is-1Type f = isProp⇒isContr-≡ f

is0Type⇒isSet : {X : 𝒰 𝒾} → isNType 2 X → isSet X
is0Type⇒isSet f = is-1Type⇒isProp (f _ _)

isSet⇒is0Type : {X : 𝒰 𝒾} → isSet X → isNType 2 X
isSet⇒is0Type f x y = isProp⇒is-1Type f

-- Theorem 7.1.4.
◁-isNType⇒isNType : (n : ℕ) {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A ◁ B)
                         → isNType n B
                         → isNType n A
◁-isNType⇒isNType 0 s f = retraction-isContr⇒isContr s f
◁-isNType⇒isNType (succ n) rs f a₁ a₂ =
  ◁-isNType⇒isNType n ret (f (s a₁) (s a₂))
 where
  r = retraction rs
  s = section rs
  ε = retract-equation rs
  t : (s a₁ ≡ s a₂) → (a₁ ≡ a₂)
  t q = (ε a₁)⁻¹ ∙ ap r q ∙ ε a₂
  ret : (a₁ ≡ a₂) ◁ (s a₁ ≡ s a₂)
  ret = t , ap s , htpy
   where
    htpy : t ∘ ap s ∼ id
    htpy p = begin
     ((ε a₁)⁻¹ ∙ ap r (ap s p)) ∙ ε a₂  ≡⟨ ∙-assoc _ ⟩
     (ε a₁)⁻¹ ∙ (ap r (ap s p) ∙ ε a₂)  ≡˘⟨ ap (λ - → (ε a₁)⁻¹ ∙ (- ∙ ε a₂))
                                               (ap-∘ _ _ _) ⟩
     (ε a₁)⁻¹ ∙ ((ap (r ∘ s) p) ∙ ε a₂) ≡˘⟨ ap ((ε a₁)⁻¹ ∙_)
                                               (∼-naturality _ _ ε) ⟩
     (ε a₁)⁻¹ ∙ (ε a₁ ∙ ap id p)        ≡⟨ ap (λ - → (ε a₁)⁻¹ ∙ (ε a₁ ∙ -))
                                              (ap-id _) ⟩
     (ε a₁)⁻¹ ∙ (ε a₁ ∙ p)              ≡˘⟨ ∙-assoc _ ⟩
     ((ε a₁)⁻¹ ∙ ε a₁) ∙ p              ≡⟨ ap (_∙ p) (⁻¹-left∙ _) ⟩
     (refl a₁) ∙ p                      ≡⟨ refl-left ⟩
     p ∎

-- Corollary 7.1.5.
≃-isNType⇒isNType : (n : ℕ) {A : 𝒰 𝒾} {B : 𝒰 𝒿}
                  → (A ≃ B)
                  → isNType n A
                  → isNType n B
≃-isNType⇒isNType n eqv f =
  ◁-isNType⇒isNType n (≃-→ eqv , ≃-← eqv , ≃-ε eqv) f

-- Theorem 7.1.6.
isEmbedding-isNType⇒isNType :
                (n : ℕ) {X : 𝒰 𝒾} {Y : 𝒰 𝒿}
              → (f : X → Y)
              → isEmbedding f
              → isNType (succ n) Y
              → isNType (succ n) X
isEmbedding-isNType⇒isNType n f e p x y =
  ≃-isNType⇒isNType n (≃-sym (ap f , e x y)) (p (f x) (f y))

-- Theorem 7.1.7.
cumul-isNType : (n : ℕ) {A : 𝒰 𝒾}
             → isNType n A
             → isNType (succ n) A
cumul-isNType 0 (c , p) x y = ((p x)⁻¹ ∙ (p y)) , contraction
  where
    contraction : (q : x ≡ y) → p x ⁻¹ ∙ p y ≡ q
    contraction (refl x) = ⁻¹-left∙ _
cumul-isNType (succ n) f x y = cumul-isNType n (f x y)

-- Theorem 7.1.8.
isNType-Σ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} (n : ℕ)
          → isNType n A
          → ((a : A) → isNType n (B a))
          → isNType n (Σ B)
isNType-Σ 0 (a₀ , p) g =
  (a₀ , pr₁ (g a₀)) , λ (a , b) → pair⁼(p a , ((pr₂ (g a) _)⁻¹ ∙ pr₂ (g a) b))
isNType-Σ {B = B} (succ n) f g (a₁ , b₁) (a₂ , b₂) =
  ≃-isNType⇒isNType n (≃-sym paths≃) Σ-isNType
  where
    paths≃ : ((a₁ , b₁) ≡ (a₂ , b₂)) ≃ (Σ p ꞉ (a₁ ≡ a₂) , tr B p b₁ ≡ b₂)
    paths≃ = ≡-Σ-≃ _ _
    Σ-isNType : isNType n (Σ p ꞉ (a₁ ≡ a₂) , tr B p b₁ ≡ b₂)
    Σ-isNType = isNType-Σ n (f a₁ a₂) lemma
      where
        lemma : (a : a₁ ≡ a₂) → isNType n (tr B a b₁ ≡ b₂)
        lemma (refl _) = g a₁ b₁ b₂

-- Theorem 7.1.9.
isNType-Π : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} (n : ℕ)
          → ((a : A) → isNType n (B a))
          → isNType n (Π B)
isNType-Π 0 p = isContr-Π p
isNType-Π (succ n) p f g =
  ≃-isNType⇒isNType n (≃-sym (≡-Π-≃ f g))
    (isNType-Π n λ x → p x (f x) (g x))

-- Theorem 7.1.10.
isProp-isNType : (n : ℕ) (A : 𝒰 𝒾)
               → isProp (isNType n A)
isProp-isNType 0 A = isProp-isContr A
isProp-isNType (succ n) A =
  isProp-Π (λ x → isProp-Π (λ y → isProp-isNType n (x ≡ y)))

NType𝒰 : (n : ℕ) (𝒾 : Level) → 𝒰 (𝒾 ⁺)
NType𝒰 n 𝒾 = Σ A ꞉ (𝒰 𝒾) , isNType n A

≡-isNType𝒰-≃ : (n : ℕ) (X Y : NType𝒰 n 𝒿) → (X ≡ Y) ≃ (pr₁ X ≡ pr₁ Y)
≡-isNType𝒰-≃ n X Y = (f , invs⇒equivs f ( g , ε , η ))
 where
  f = ap pr₁
  g = λ - → pair⁼(- , isProp-isNType n _ _ _)
  ε = λ - → ≡-Σ-comp₁ _ _
  η : g ∘ f ∼ id
  η p = begin
    pair⁼(ap pr₁ p , isProp-isNType n _ _ _) ≡⟨ i ⟩
    pair⁼(ap pr₁ p , pair⁼⁻¹₂ p)             ≡⟨ ii ⟩
    p ∎
   where
    i = ap (λ - → pair⁼(ap pr₁ p , -))
           ((isProp⇒isSet (isProp-isNType n _)) _ _)
    ii = ≃-η (≡-Σ-≃ _ _) p

isEmbedding-pr₁-isNType𝒰-≃ :
     (n : ℕ)
     (X X' : NType𝒰 n 𝒾)
   → isEmbedding (pr₁ {B = (λ f → isEquiv {A = pr₁ X} {B = pr₁ X'} f)})
isEmbedding-pr₁-isNType𝒰-≃ n (X , p) (X' , p') (f , equiv-f) (g , equiv-g) =
  invs⇒equivs (ap pr₁) (h , ε , η)
 where
  h : f ≡ g → f , equiv-f ≡ g , equiv-g
  h k = pair⁼(k , isProp-isEquiv g (tr isEquiv k equiv-f) equiv-g)
  ε : (ap pr₁) ∘ h ∼ id
  ε k = ≡-Σ-comp₁ k (isProp-isEquiv g (tr isEquiv k equiv-f) equiv-g)
  η : h ∘ (ap pr₁) ∼ id
  η equiv = begin
    pair⁼(ap pr₁ equiv , isProp-isEquiv g _ equiv-g) ≡⟨ i ⟩
    pair⁼(ap pr₁ equiv , pair⁼⁻¹₂ equiv)             ≡⟨ ii ⟩
    equiv ∎
   where
    i = ap (λ - → pair⁼(ap pr₁ equiv , -))
           (isProp⇒isSet (isProp-isEquiv g) _ _)
    ii = ≃-η (≡-Σ-≃ _ _) equiv

-- Theorem 7.1.11.
isNType-isNType : (n : ℕ)
                → isNType (succ n) (NType𝒰 n 𝒾)
isNType-isNType 0 (X , p) (X' , p') =
   ≃-isNType⇒isNType 0 (≃-sym (≡-isNType𝒰-≃ 0 (X , p) (X' , p')))
     (≃-isNType⇒isNType 0 (≃-sym (≡-𝒰-≃ X X'))
       (isPointedProp⇒isContr (X ≃ X')
         (≃-trans (isContr⇒≃𝟙 X p) (≃-sym (isContr⇒≃𝟙 X' p')) ,
          (λ f g →
            pair⁼(
              funext (λ x → isContr⇒isProp X' p' (pr₁ f x) (pr₁ g x)) ,
              isProp-isEquiv _ _ _)))))
 where
  X≃1 = isContr⇒≃𝟙 X p
  X'≃1 = isContr⇒≃𝟙 X' p'
isNType-isNType (succ n) X X' =
   ≃-isNType⇒isNType (succ n) (≃-sym (≡-isNType𝒰-≃ (succ n) X X'))
     (≃-isNType⇒isNType (succ n) (≃-sym (≡-𝒰-≃ (pr₁ X) (pr₁ X')))
       (isEmbedding-isNType⇒isNType n pr₁
         (isEmbedding-pr₁-isNType𝒰-≃ (succ n) X X')
         (isNType-Π (succ n) λ _ → (pr₂ X')) )) 
```

## 7.2. Uniqueness of identity proofs and Hedberg’s theorem

```agda
hasAxiomK : 𝒰 𝒾 → 𝒰 𝒾
hasAxiomK X = {x : X} (p : x ≡ x) → (p ≡ refl x)

-- Theorem 7.2.1.
isSet⇒hasAxiomK : {X : 𝒰 𝒾} → isSet X → hasAxiomK X
isSet⇒hasAxiomK f p = f p (refl _)

hasAxiomK⇒isSet : {X : 𝒰 𝒾} → hasAxiomK X → isSet X
hasAxiomK⇒isSet f p (refl x) = f p

-- Theorem 7.2.2.
mereRelation⇒≡⇒isSet :
       {X : 𝒰 𝒾} (R : mereRelation X 𝒿)
     → ((x : X) → pr₁ (R(x , x)))
     → ((x y : X) → pr₁ (R(x , y)) → x ≡ y)
     → isSet X
mereRelation⇒≡⇒isSet R ρ f =
 hasAxiomK⇒isSet (λ {x} p → ∙-left-cancel (f x x (ρ x)) (begin
  f x x (ρ x) ∙ p                  ≡˘⟨ tr-Homc─ x p (f x x (ρ x)) ⟩
  tr (λ v → x ≡ v) p (f x x (ρ x)) ≡⟨ ≃-→ (≡-tr-Π-≃ p (f x x) (f x x))
                                          (apd (f x) p) (ρ x) ⟩
  f x x (tr (λ v → pr₁ (R (x , v)))
            p (ρ x))               ≡⟨ ap (f x x) (pr₂ (R(x , x)) _ _) ⟩
  f x x (ρ x)                      ≡˘⟨ refl-right ⟩
  f x x (ρ x) ∙ refl x             ∎))

-- Corollary 7.2.3.
hasRAA-Equality⇒isSet :
       {X : 𝒰 𝒾}
     → ((x y : X) → ¬¬(x ≡ y) → (x ≡ y))
     → isSet X
hasRAA-Equality⇒isSet f =
  mereRelation⇒≡⇒isSet
    (λ (x , y) → ¬¬(x ≡ y)
    , λ g h → funext (λ - → isProp-𝟘 _ _))
    (λ x → λ p → p (refl x))
    f

-- Lemma 7.2.4.
isDecidable⇒hasRAA :
    {A : 𝒰 𝒾}
  → isDecidable A
  → hasRAA A
isDecidable⇒hasRAA {A = A} f =
  ⊎-rec (¬¬ A → A) (λ a - → a) (λ f g → !𝟘 A (g f) ) f

-- Theorem 7.2.5.
Hedberg : {X : 𝒰 𝒾}
        → hasDecidableEquality X
        → isSet X
Hedberg f =
  hasRAA-Equality⇒isSet
    (λ x y → isDecidable⇒hasRAA (f x y))

-- Theorem 7.2.6.
hasDecidableEquality-ℕ : hasDecidableEquality ℕ
hasDecidableEquality-ℕ zero zero = inl (refl zero)
hasDecidableEquality-ℕ zero (succ y) = inr (¬0≡succ y)
hasDecidableEquality-ℕ (succ x) zero = inr (¬succ≡0 x)
hasDecidableEquality-ℕ (succ x) (succ y) =
  ⊎-rec (isDecidable (succ x ≡ succ y))
        (λ p → inl(ap succ p))
        (λ f → inr(λ p → f (sm≡sn⇒m≡n p)))
        (hasDecidableEquality-ℕ x y)

-- Lemma 7.2.8.
inhab-isNType⇒isNType : {X : 𝒰 𝒾} (n : ℕ)
                      → ((x : X) → isNType (succ n) X)
                      → isNType (succ n) X
inhab-isNType⇒isNType n f x y = f x x y

-- Theorem 7.2.7.
isNType⇒isNType-Ω : {X : 𝒰 𝒾} (n : ℕ)
                 → (isNType (succ (succ n)) X)
                 → ((x : X) → isNType (succ n) (x ≡ x))
isNType⇒isNType-Ω n p x = p x x

isNType-Ω⇒isNType : {X : 𝒰 𝒾} (n : ℕ)
                 → ((x : X) → isNType (succ n) (x ≡ x))
                 → (isNType (succ (succ n)) X)
isNType-Ω⇒isNType n f x x' = inhab-isNType⇒isNType n lemma
  where
    lemma : x ≡ x' → isNType (succ n) (x ≡ x')
    lemma (refl x) = f x

-- Theorem 7.2.9.
isNType⇒isContr-Ω : {A : 𝒰 𝒾} (n : ℕ)
                  → isNType (succ n) A
                  → ((a : A) → isContr (pr₁ (Ωⁿ n (A , a))))
isNType⇒isContr-Ω 0 f a = isProp⇒inhab→isContr (is-1Type⇒isProp f) a
isNType⇒isContr-Ω 1 f a =
  (refl a , λ p → (isSet⇒hasAxiomK (is0Type⇒isSet f) p)⁻¹)
isNType⇒isContr-Ω (succ (succ n)) f a =
  (isNType⇒isContr-Ω (succ n) (isNType⇒isNType-Ω (succ n) f a)) (refl a)

isContr-Ω⇒isNType : {A : 𝒰 𝒾} (n : ℕ)
                  → ((a : A) → isContr (pr₁ (Ωⁿ n (A , a))))
                  → isNType (succ n) A
isContr-Ω⇒isNType 0 f = isProp⇒is-1Type (inhab→isContr⇒isProp f)
isContr-Ω⇒isNType 1 f =
  isSet⇒is0Type (hasAxiomK⇒isSet λ p → (pr₂ (f _) p)⁻¹ ∙ (pr₂ (f _) (refl _)))
isContr-Ω⇒isNType {A = A} (succ (succ n)) f =
  isNType-Ω⇒isNType (succ n)
    (λ a → isContr-Ω⇒isNType (succ n)
             (λ p → tr isContr (ap (pr₁ ∘ Ωⁿ n) (lemma a p)) (f a)))
 where
  lemma : (a : A) (p : a ≡ a)
        → (Ω ((a ≡ a) , refl a)) ≡ (Ω ((a ≡ a) , p))
  lemma a p = (pair⁼(ua eqv , ((≡-𝒰-comp eqv (pr₂ (Ω ((a ≡ a) , p))))
       ∙ (ap (_∙ ⁻¹-right∙ p) refl-right ) ∙ ⁻¹-left∙ (⁻¹-right∙ p))))⁻¹
   where
    eqv : pr₁ (Ω ((a ≡ a) , p)) ≃ pr₁ (Ω ((a ≡ a) , refl a))
    eqv =
     ((_ , isEquiv⇒isEquiv-ap (_∙ p ⁻¹) (invs⇒equivs _ (isQinv-─∙ (p ⁻¹))) p p)
       ≃∙ (_ , invs⇒equivs _ (isQinv-∙─ ((⁻¹-right∙ p)⁻¹)))
       ≃∙ (_ , invs⇒equivs _ (isQinv-─∙ (⁻¹-right∙ p))))
```

## 7.3. Truncations

```agda
postulate -- take care of numbers...
  ∥_∥ₙ : {𝒾 : Level} → (A : 𝒰 𝒾) → (n : ℕ) → 𝒰 𝒾
  ∣_∣ₙ : {𝒾 : Level} → {A : 𝒰 𝒾} → A → (n : ℕ) → ∥ A ∥ₙ n
  ∥∥ₙ-hub : {𝒾 : Level} {A : 𝒰 𝒾} (n : ℕ)
         → (𝕊ⁿ n → ∥ A ∥ₙ (succ n))
         → (∥ A ∥ₙ (succ n))
  ∥∥ₙ-spoke : {𝒾 : Level} {A : 𝒰 𝒾} (n : ℕ)
            → (r : 𝕊ⁿ n → ∥ A ∥ₙ (succ n))
            → (x : 𝕊ⁿ n) → (r x ≡ ∥∥ₙ-hub n r)
  ∥∥₋₂ : {𝒾 : Level} → (A : 𝒰 𝒾) → ∥ A ∥ₙ 0 ≃ 𝟙

-- Lemma 7.3.1.
isNType-∥∥ₙ : (A : 𝒰 𝒾) → (n : ℕ) → isNType n (∥ A ∥ₙ n)
isNType-∥∥ₙ A zero = ≃𝟙⇒isContr (∥ A ∥ₙ zero) (∥∥₋₂ A)
isNType-∥∥ₙ A (succ n) =
  isContr-Ω⇒isNType n
    (λ b → ≃-isNType⇒isNType 0 (Map*𝕊ⁿ→-≃Ωⁿ n (∥ A ∥ₙ (succ n) , b)) (lemma b))
 where
  lemma : (b : ∥ A ∥ₙ (succ n))
        → isContr (Map* (𝕊ⁿ n , N𝕊ⁿ n) (∥ A ∥ₙ (succ n) , b))
  lemma b = (((λ x → b) , refl b) , contr)
   where
    contr : ((r , p) : Map* (𝕊ⁿ n , N𝕊ⁿ n) (∥ A ∥ₙ (succ n) , b))
          → ((λ x → b) , refl b) ≡ (r , p)
    contr (r , p) = pair⁼(funext htpy , (begin
      tr (λ f → f (N𝕊ⁿ n) ≡ b) (funext htpy) (refl b)  ≡⟨ i ⟩
      (ap (λ f → f (N𝕊ⁿ n)) (funext htpy))⁻¹ ∙ refl b
        ∙ ap (λ _ → b) (funext htpy)                   ≡⟨ ii ⟩
      (ap (λ f → f (N𝕊ⁿ n)) (funext htpy))⁻¹
        ∙ ap (λ _ → b) (funext htpy)                   ≡⟨ iii ⟩
      (ap (λ f → f (N𝕊ⁿ n)) (funext htpy))⁻¹
        ∙ refl _ ≡⟨ iv ⟩
      (ap (λ f → f (N𝕊ⁿ n)) (funext htpy))⁻¹           ≡⟨ v ⟩
      (p ⁻¹ ∙ ∥∥ₙ-spoke n r (N𝕊ⁿ n)
        ∙ ((∥∥ₙ-spoke n r ((N𝕊ⁿ n)))⁻¹))⁻¹             ≡⟨ vi ⟩
      (p ⁻¹ ∙ (∥∥ₙ-spoke n r (N𝕊ⁿ n)
        ∙ ((∥∥ₙ-spoke n r ((N𝕊ⁿ n)))⁻¹)))⁻¹            ≡⟨ vii ⟩
      (p ⁻¹ ∙ refl _)⁻¹                                ≡⟨ viii ⟩
      (p ⁻¹)⁻¹                                         ≡⟨ ix ⟩
      p ∎))
     where
      htpy = λ x → p ⁻¹ ∙ ∥∥ₙ-spoke n r (N𝕊ⁿ n) ∙ ((∥∥ₙ-spoke n r x)⁻¹)
      i = tr-fx≡gx (λ f → f (N𝕊ⁿ n)) (λ _ → b) _ (refl b)
      ii = ap (_∙ ap (λ _ → b) (funext htpy)) refl-right
      iii = ap ((ap (λ f → f (N𝕊ⁿ n)) (funext htpy))⁻¹ ∙_) (ap-const _ b)
      iv = refl-right
      v = ap (_⁻¹) (happly (≡-Π-comp htpy) (N𝕊ⁿ n))
      vi = ap (_⁻¹) (∙-assoc (p ⁻¹))
      vii = ap (λ - → (p ⁻¹ ∙ -)⁻¹) (⁻¹-right∙ (∥∥ₙ-spoke n r (N𝕊ⁿ n)))
      viii = ap (_⁻¹) refl-right
      ix = ⁻¹-involutive p
```
