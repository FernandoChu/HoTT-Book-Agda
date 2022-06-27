{-# OPTIONS --without-K --exact-split --safe --auto-inline --no-import-sorts #-}

module Chapter4.Book where

open import Chapter3.Exercises public

---------------------------------------------------------------------------------

-- 4.1 Quasi-inverses

---------------------------------------------------------------------------------

-- 4.2 Half adjoint equivalences

-- Definition 4.2.1.
ishae : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 (𝒾 ⊔ 𝒿)
ishae f = Σ g ꞉ (codomain f → domain f)
         , Σ η ꞉ g ∘ f ∼ id
         , Σ ε ꞉ f ∘ g ∼ id
         , ((x : domain f) → ap f (η x) ≡ ε (f x))

ishae→qinv : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y)
           → ishae f → qinv f
ishae→qinv f (g , η , ε , τ) = g , ε , η

-- Theorem 4.2.3.
invertibles-are-haes : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y)
                     → qinv f → ishae f
invertibles-are-haes f (g , ε , η) = g , η , ε' , τ
 where
  ε' = λ y → begin f (g y)   ≡⟨ (ε (f (g y)))⁻¹ ⟩
             f (g (f (g y))) ≡⟨ ap f (η (g y))  ⟩
             ε y

  module _ (x : domain f) where

   p = η (g (f x))       ≡⟨ ~-id-naturality (g ∘ f) η  ⟩
       ap (g ∘ f) (η x)  ≡⟨ ap-∘ f g (η x)             ⟩
       ap g (ap f (η x)) ∎

   q = ap f (η (g (f x))) ∙ ε (f x)          ≡⟨ by-p            ⟩
       ap f (ap g (ap f (η x))) ∙ ε (f x)    ≡⟨ by-ap-∘         ⟩
       ap (f ∘ g) (ap f (η x))  ∙ ε (f x)    ≡⟨ by-∼-naturality ⟩
       ε (f (g (f x))) ∙ ap id (ap f (η x))  ≡⟨ by-ap-id        ⟩
       ε (f (g (f x))) ∙ ap f (η x)          ∎
    where
     by-p            = ap (λ - → ap f - ∙ ε (f x)) p
     by-ap-∘         = ap (_∙ ε (f x)) ((ap-∘ g f (ap f (η x)))⁻¹)
     by-∼-naturality = (∼-naturality (f ∘ g) id ε)⁻¹
     by-ap-id        = ap (ε (f (g (f x))) ∙_) (ap-id (ap f (η x)))

   τ = ap f (η x)                                           ≡⟨ refl-left ⁻¹ ⟩
       refl (f (g (f x)))                     ∙ ap f (η x)  ≡⟨ by-⁻¹-left∙  ⟩
       (ε (f (g (f x))))⁻¹ ∙  ε (f (g (f x))) ∙ ap f (η x)  ≡⟨ by-∙assoc    ⟩
       (ε (f (g (f x))))⁻¹ ∙ (ε (f (g (f x))) ∙ ap f (η x)) ≡⟨ by-q         ⟩
       (ε (f (g (f x))))⁻¹ ∙ (ap f (η (g (f x))) ∙ ε (f x)) ≡⟨ refl _       ⟩
       ε' (f x)                                             ∎
    where
     by-⁻¹-left∙ = ap (_∙ ap f (η x)) ((⁻¹-left∙ (ε (f (g (f x)))))⁻¹)
     by-∙assoc   = ∙-assoc ((ε (f (g (f x))))⁻¹)
     by-q        = ap ((ε (f (g (f x))))⁻¹ ∙_) (q ⁻¹)

-- Definition 4.2.4.
fib : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) → B → 𝒰 (𝒾 ⊔ 𝒿)
fib f y = Σ x ꞉ domain f , f x ≡ y

-- Helper for the next lemma
≡-comm : (is-univalent 𝒾)
       → {A : 𝒰 𝒾} {x y : A}
       → (p q : x ≡ y) → (p ≡ q) ≡ (q ≡ p)
≡-comm u p q = ua u eqv
  where
    eqv : (p ≡ q) ≃ (q ≡ p)
    eqv = (_⁻¹) , invs-are-equivs (_⁻¹)
                   ((_⁻¹) , ⁻¹-involutive , ⁻¹-involutive)

-- Lemma 4.2.5.
fib-≡-≃ : {𝒾 𝒿 : Level} {A : 𝒰 𝒾} {B : 𝒰 𝒿}
        → is-univalent 𝒿
        → has-funext 𝒾 (𝒿 ⁺)
        → (f : A → B) (y : B)
          ((x , p) (x' , p') : fib f y)
        → ((x , p) ≡ (x' , p')) ≃ (Σ γ ꞉ (x ≡ x') , ap f γ ∙ p' ≡ p)
fib-≡-≃ u fe f y (x , p) (x' , p') =
  tr (λ - → ((x , p) ≡ (x' , p')) ≃ -) ≡fams Σ-≡-≃
 where
  const-y = λ _ → y
  ap-const : (p : x' ≡ x) → ap const-y p ≡ refl y
  ap-const (refl x') = refl _

  ∼fams : (λ γ → tr (λ - → f - ≡ y) γ p ≡ p') ∼ (λ γ → ap f γ ∙ p' ≡ p)
  ∼fams γ = begin
   (tr (λ - → f - ≡ y) γ p ≡ p')      ≡⟨ by-tr-γ⁻¹ γ ⟩
   (p ≡ tr (λ - → f - ≡ y) (γ ⁻¹) p') ≡⟨ ap (p ≡_) tr-lemma ⟩
   (p ≡ ap f γ ∙ p')                  ≡⟨ ≡-comm u p (ap f γ ∙ p') ⟩
   (ap f γ ∙ p' ≡ p)                  ∎
   where
    by-tr-γ⁻¹ : (γ : (x ≡ x'))
              → (tr (λ - → f - ≡ y) γ p ≡ p')
                  ≡ (p ≡ tr (λ - → f - ≡ y) (γ ⁻¹) p')
    by-tr-γ⁻¹ (refl x) = refl _

    tr-lemma : tr (λ - → f - ≡ y) (γ ⁻¹) p' ≡ ap f γ ∙ p'
    tr-lemma = begin
     tr (λ - → f - ≡ y) (γ ⁻¹) p'               ≡⟨⟩
     tr (λ - → f - ≡ const-y -) (γ ⁻¹) p'       ≡⟨ i ⟩
     (ap f (γ ⁻¹))⁻¹ ∙ p' ∙ (ap const-y (γ ⁻¹)) ≡⟨ ii ⟩
     (ap f (γ ⁻¹))⁻¹ ∙ p' ∙ (refl _)            ≡⟨ iii ⟩
     (ap f (γ ⁻¹))⁻¹ ∙ (p' ∙ (refl _))          ≡⟨ iv ⟩
     (ap f (γ ⁻¹))⁻¹ ∙ p'                       ≡⟨ v ⟩
     ap f ((γ ⁻¹)⁻¹) ∙ p'                       ≡⟨ vi ⟩
     ap f γ ∙ p'                                ∎
      where
       i = tr-fx≡gx f const-y (γ ⁻¹) p'
       ii = ap (λ - → (ap f (γ ⁻¹))⁻¹ ∙ p' ∙ -) (ap-const (γ ⁻¹))
       iii = ∙-assoc ((ap f (γ ⁻¹))⁻¹)
       iv = ap ((ap f (γ ⁻¹))⁻¹ ∙_) refl-right
       v = ap (_∙ p') (ap⁻¹ f (γ ⁻¹))
       vi = ap (λ - → ap f - ∙ p') (⁻¹-involutive γ)

  ≡fams : (Σ (λ γ → tr (λ - → f - ≡ y) γ p ≡ p')) ≡ (Σ (λ γ → ap f γ ∙ p' ≡ p))
  ≡fams = ap Σ (funext fe ∼fams)


-- Theorem 4.2.6.
ishae→contr-fib≡-≃ : {𝒾 𝒿 : Level} {A : 𝒰 𝒾} {B : 𝒰 𝒿}
                   → is-univalent 𝒿
                   → has-funext 𝒾 (𝒿 ⁺)
                   → (f : A → B) → (ishae f) → (y : B)
                   → isContr (fib f y)
ishae→contr-fib≡-≃ u fe f (g , η , ε , τ) y = center , contraction
 where
  center = (g y , ε y)
  contraction : (xp : fib f y) → center ≡ xp
  contraction (x , p) = sufficient (γ , fγ∙p≡εγ)
   where
    sufficient : (Σ γ ꞉ g y ≡ x , ap f γ ∙ p ≡ ε y) → center ≡ (x , p)
    sufficient = Eq→fun (≃-sym (fib-≡-≃ u fe f y center (x , p)))
    γ = (ap g p)⁻¹ ∙ η x
    fγ∙p≡εγ : ap f γ ∙ p ≡ ε y
    fγ∙p≡εγ = begin
     ap f γ ∙ p                                ≡⟨ i ⟩
     ap f ((ap g p)⁻¹) ∙ ap f (η x) ∙ p        ≡⟨ ii ⟩
     ap f ((ap g p)⁻¹) ∙ ε (f x) ∙ p           ≡⟨ iii ⟩
     ap f ((ap g p)⁻¹) ∙ (ε (f x) ∙ p)         ≡⟨ iv ⟩
     ap f ((ap g p)⁻¹) ∙ (ε (f x) ∙ ap id p)   ≡⟨ v ⟩
     ap f ((ap g p)⁻¹) ∙ (ap (f ∘ g) p ∙ ε y)  ≡⟨ vi ⟩
     ap f (ap g (p ⁻¹)) ∙ (ap (f ∘ g) p ∙ ε y) ≡⟨ vii ⟩
     ap (f ∘ g) (p ⁻¹) ∙ (ap (f ∘ g) p ∙ ε y)  ≡⟨ viii ⟩
     ap (f ∘ g) (p ⁻¹) ∙ ap (f ∘ g) p ∙ ε y    ≡⟨ ix ⟩
     ap (f ∘ g) (p ⁻¹ ∙ p) ∙ ε y               ≡⟨ x' ⟩
     refl (f (g y)) ∙ ε y                      ≡⟨ xi ⟩
     ε y                                       ∎
     where
      i = ap (_∙ p) (ap-∙ f ((ap g p)⁻¹) (η x))
      ii = ap (λ - → ap f ((ap g p)⁻¹) ∙ - ∙ p) (τ x)
      iii = ∙-assoc (ap f ((ap g p)⁻¹))
      iv = ap (λ - → ap f ((ap g p)⁻¹) ∙ (ε (f x) ∙ -)) ((ap-id p)⁻¹)
      v = ap (ap f ((ap g p)⁻¹) ∙_) (∼-naturality (f ∘ g) id ε)
      vi = ap (λ - → ap f - ∙ (ap (f ∘ g) p ∙ ε y)) (ap⁻¹ g p)
      vii = ap (_∙ (ap (f ∘ g) p ∙ ε y)) ((ap-∘ g f (p ⁻¹))⁻¹)
      viii = (∙-assoc (ap (f ∘ g) (p ⁻¹)))⁻¹
      ix = ap (_∙ ε y) ((ap-∙ (f ∘ g) (p ⁻¹) p)⁻¹)
      x' = ap (λ - → ap (f ∘ g) - ∙ ε y) (⁻¹-left∙ p)
      xi = refl-left

-- Definition 4.2.7.
linv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) → 𝒰 (𝒾 ⊔ 𝒿)
linv {𝒾} {𝒿} {A} {B} f = Σ g ꞉ (B → A) , (g ∘ f) ∼ id

rinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) → 𝒰 (𝒾 ⊔ 𝒿)
rinv {𝒾} {𝒿} {A} {B} f = Σ g ꞉ (B → A) , (f ∘ g) ∼ id

-- Lemma 4.2.8.
qinv→f∘- : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
         → has-funext 𝓀 𝒿 → has-funext 𝓀 𝒾
         → (f : A → B)
         → qinv f → (qinv (λ (- : C → A) → f ∘ -))
qinv→f∘- fe1 fe2 f (g , f∘g , g∘f) =
  ((g ∘_) , ∼₁ , ∼₂)
 where
  ∼₁ : (f ∘_) ∘ (g ∘_) ∼ id
  ∼₁ α = funext fe1 (λ x → f∘g (α x))
  ∼₂ : (g ∘_) ∘ (f ∘_) ∼ id
  ∼₂ β = funext fe2 (λ x → g∘f (β x))

qinv→-∘f : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
         → has-funext 𝒾 𝓀 → has-funext 𝒿 𝓀
         → (f : A → B)
         → qinv f → (qinv (λ (- : B → C) → - ∘ f))
qinv→-∘f fe1 fe2 f (g , f∘g , g∘f) =
  ((_∘ g) , ∼₁ , ∼₂)
 where
  ∼₁ : (_∘ f) ∘ (_∘ g) ∼ id
  ∼₁ α = funext fe1 (λ x → ap α (g∘f x))
  ∼₂ : (_∘ g) ∘ (_∘ f) ∼ id
  ∼₂ β = funext fe2 (λ x → ap β (f∘g x))

-- Lemma 4.2.9.
qinv→linv-isContr : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
         → has-funext (𝒾 ⊔ 𝒿) (𝒾 ⁺)
         → has-funext 𝒿 𝒾
         → has-funext 𝒾 𝒾
         → is-univalent 𝒾
         → (f : A → B)
         → qinv f → isContr (linv f)
qinv→linv-isContr fe1 fe2 fe3 u f qinvf =
  tr isContr (i ⁻¹) v
 where
  i : linv f ≡ (Σ g ꞉ (codomain f → domain f) , g ∘ f ≡ id)
  i = ap Σ (funext fe1 htpy)
   where
    htpy : (h : codomain f → domain f) → (h ∘ f ∼ id) ≡ (h ∘ f ≡ id)
    htpy h = ua u (≃-sym (happly , fe3 (h ∘ f) id))
  iii : qinv (_∘ f)
  iii = qinv→-∘f fe3 fe2 f qinvf
  iv : ishae (_∘ f)
  iv = invertibles-are-haes (_∘ f) iii
  v : isContr (fib (_∘ f) id)
  v = ishae→contr-fib≡-≃ u fe1 (_∘ f) iv id

---------------------------------------------------------------------------------

-- 4.3 Bi-invertible maps

isequiv-isProp : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (f : A → B) → isProp (is-equiv f)
isequiv-isProp f = _
