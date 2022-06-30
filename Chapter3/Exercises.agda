module Chapter3.Exercises where

open import Chapter3.Book public

-- Exercise 3.4
prop-if-endo-are-contr : has-funext 𝒾 𝒾 → (A : 𝒰 𝒾) → isProp A → isContr (A → A)
prop-if-endo-are-contr fe A h = (id , p)
  where
    p : (g : A → A) → id ≡ g
    p g = (pr₁ (pr₁ (fe id g))) (λ x → h x (g x))

contr-endo-implies-prop : (A : 𝒰 𝒾) → isContr (A → A) → isProp A
contr-endo-implies-prop A h x y = happly (A→A-isProp f g) x
  where
    A→A-isProp : isProp (A → A)
    A→A-isProp = pr₂ (contr-are-pointed-props (A → A) h)
    f : A → A
    f - = x
    g : A → A
    g - = y

-- Exercise 3.5
isProp-implies-point→isContr : {A : 𝒰 𝒾}
    → isProp A → (A → isContr A)
isProp-implies-point→isContr fp c = (c , λ x → fp c x)

point→isContr-implies-isProp : {A : 𝒰 𝒾}
    → (A → isContr A) → isProp A
point→isContr-implies-isProp g x y =
  pr₂ (contr-are-pointed-props (domain g) (g x)) x y

isProp≃point→isContr : {A : 𝒰 𝒾}
    → has-funext 𝒾 𝒾
    → isProp A ≃ (A → isContr A)
isProp≃point→isContr {𝒾} {A} fe = (isProp-implies-point→isContr ,
  invs-are-equivs isProp-implies-point→isContr
    (point→isContr-implies-isProp , ε , η))
 where
  ε : (isProp-implies-point→isContr ∘ point→isContr-implies-isProp)
        ∼ id
  ε g = funext fe (λ x → isContr-isProp fe A _ _)
  η : (point→isContr-implies-isProp ∘ isProp-implies-point→isContr)
        ∼ id
  η fp = funext fe (λ x → funext fe (λ y → props-are-sets fp _ _))

-- Exercise 3.6
isProp→isDecidible-isProp : has-funext 𝒾 lzero
                          → (A : 𝒰 𝒾) → isProp A
                          → isProp (A ⊎ (¬ A))
isProp→isDecidible-isProp fe A f (inl x) (inl y) = ap inl (f x y)
isProp→isDecidible-isProp fe A f (inl x) (inr c) = !𝟘 (inl x ≡ inr c) (c x)
isProp→isDecidible-isProp fe A f (inr c) (inl x) = !𝟘 (inr c ≡ inl x) (c x)
isProp→isDecidible-isProp fe A f (inr c) (inr d) = ap inr p
  where
    p : c ≡ d
    p = funext fe (λ x → !𝟘 (c x ≡ d x) (c x))

-- Exercise 3.7
isProp→isDecidible-isProp' : (A : 𝒰 𝒾) → (B : 𝒰 𝒿)
                          → isProp A → isProp B → ¬ (A × B)
                          → isProp (A ⊎ B)
isProp→isDecidible-isProp' A B f g c (inl a) (inl a') =
  ap inl (f a a')
isProp→isDecidible-isProp' A B f g c (inl a) (inr b) =
  !𝟘 (inl a ≡ inr b) (c (a , b))
isProp→isDecidible-isProp' A B f g c (inr b) (inl a) =
  !𝟘 (inr b ≡ inl a) (c (a , b))
isProp→isDecidible-isProp' A B f g c (inr b) (inr b') =
  ap inr (g b b')

-- Exercise 3.20
Σ-over-contr-base-≃-fiber-base : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿)
                               → ((a , f) : isContr A)
                               → (Σ x ꞉ A , P x) ≃ P a
Σ-over-contr-base-≃-fiber-base {𝒾} {𝒿} {A} P (a , f) =
  map , invs-are-equivs map (map⁻¹ , ε , η)
 where
  AisSet : isSet A
  AisSet = props-are-sets (pr₂ (contr-are-pointed-props A (a , f)))
  map = λ (x , px) → tr P ((f x)⁻¹) px
  map⁻¹ = λ pa → (a , pa)
  ε = λ pa → ap (λ - → tr P - pa) (AisSet ((f a)⁻¹) (refl a))
  η : (map⁻¹ ∘ map) ∼ id
  η (x , px) = pair⁼ (f x , s)
   where
    s : tr P (f x) (tr P ((f x)⁻¹) px) ≡ px
    s = begin
     tr P (f x) (tr P ((f x)⁻¹) px) ≡⟨ happly (tr-∘ P ((f x)⁻¹) (f x)) px ⟩
     tr P ((f x)⁻¹ ∙ (f x)) px      ≡⟨ ap (λ - → tr P - px)
                                          (AisSet ((f x)⁻¹ ∙ (f x)) (refl x)) ⟩
     px                             ∎
