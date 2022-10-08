---
title: Chapter 7. Homotopy n-types
---

# Chapter 7. Homotopy n-types

```agda
module Chapter7.Book where

open import Chapter6.Exercises public
```

```agda
-- Definition 7.1.1.
-- Nothe that this is really the property of being an n-2 type.
isNType : (n : ℕ) (A : 𝒰 𝒾) → 𝒰 𝒾
isNType 0 A        = isContr A
isNType (succ n) A = (x y : A) → isNType n (x ≡ y)

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
isNType-isNType 0 X X' =
   ≃-isNType⇒isNType 0 (≃-sym (≡-isNType𝒰-≃ 0 X X'))
     (≃-isNType⇒isNType 0 (≃-sym (≡-≡-≃ (pr₁ X) (pr₁ X')))
     {!!})

     -- {!tr (λ - → isContr (- ≡ pr₁ X')) (ua (isContr⇒≃𝟙 (pr₁ X') (pr₂ X'))) ?!}
     -- {!tr (λ - → isContr (- ≡ pr₁ X')) (ua (isContr⇒≃𝟙 (pr₁ X') (pr₂ X'))) ?!}
isNType-isNType (succ n) X X' =
   ≃-isNType⇒isNType (succ n) (≃-sym (≡-isNType𝒰-≃ (succ n) X X'))
     (≃-isNType⇒isNType (succ n) (≃-sym (≡-≡-≃ (pr₁ X) (pr₁ X')))
       (isEmbedding-isNType⇒isNType n pr₁
         (isEmbedding-pr₁-isNType𝒰-≃ (succ n) X X')
         (isNType-Π (succ n) λ _ → (pr₂ X')) ))
```
