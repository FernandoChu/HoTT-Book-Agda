---
title: Chapter 4. Equivalences
---

# Chapter 4. Equivalences

```agda
module Chapter4.Book where

open import Chapter3.Exercises public
```

## 4.1 Quasi-inverses

```agda
--
```

## 4.2 Half adjoint equivalences

```agda
-- Definition 4.2.1.
isHae : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 (𝒾 ⊔ 𝒿)
isHae f = Σ g ꞉ (codomain f → domain f)
         , Σ η ꞉ g ∘ f ∼ id
         , Σ ε ꞉ f ∘ g ∼ id
         , ((x : domain f) → ap f (η x) ≡ ε (f x))

isHae' : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 (𝒾 ⊔ 𝒿)
isHae' f = Σ g ꞉ (codomain f → domain f)
         , Σ η ꞉ g ∘ f ∼ id
         , Σ ε ꞉ f ∘ g ∼ id
         , ((y : codomain f) → ap g (ε y) ≡ η (g y))

-- Lemma 4.2.2.
isHae⇒isHae' : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
       → (f : A → B)
       → isHae f → isHae' f
isHae⇒isHae' f (g , η , ε , τ) = (g , η , ε , ν)
 where
  ν : (y : codomain f) → (ap g (ε y) ≡ η (g y))
  ν y = ∙-left-cancel (ap (g ∘ f ∘ g) (ε y)) (square3 ⁻¹ ∙ square4)
   where
    square0 : ε (f (g y)) ∙ (ε y) ≡ ap (f ∘ g) (ε y) ∙ (ε y)
    square0 = tr (λ - → ε (f (g y)) ∙ - ≡ ap (f ∘ g) (ε y) ∙ (ε y))
                 (ap-id (ε y)) (∼-naturality (f ∘ g) id ε)
    square1 : ap g (ε (f (g y))) ∙ ap g (ε y)
               ≡ ap (g ∘ f ∘ g) (ε y) ∙ ap g (ε y)
    square1 = begin
      ap g (ε (f (g y))) ∙ ap g (ε y)      ≡˘⟨ i  ⟩
      ap g (ε (f (g y)) ∙ (ε y))           ≡⟨ ii  ⟩
      ap g (ap (f ∘ g) (ε y) ∙ (ε y))      ≡⟨ iii ⟩
      ap g (ap (f ∘ g) (ε y)) ∙ ap g (ε y) ≡˘⟨ iv ⟩
      ap (g ∘ f ∘ g) (ε y) ∙ ap g (ε y)    ∎
     where
      i = ap-∙ g (ε (f (g y))) (ε y)
      ii = ap (ap g) square0
      iii = ap-∙ g (ap (f ∘ g) (ε y)) (ε y)
      iv = ap (_∙ ap g (ε y)) (ap-∘ (f ∘ g) g (ε y))
    square2 : ap (g ∘ f) (η (g y)) ∙ ap g (ε y)
               ≡ ap (g ∘ f ∘ g) (ε y) ∙ ap g (ε y)
    square2 = begin
      ap (g ∘ f) (η (g y)) ∙ ap g (ε y)  ≡⟨ i   ⟩
      ap g (ap f (η (g y))) ∙ ap g (ε y) ≡⟨ ii  ⟩
      ap g (ε (f (g y))) ∙ ap g (ε y)    ≡⟨ iii ⟩
      ap (g ∘ f ∘ g) (ε y) ∙ ap g (ε y) ∎
     where
      i = ap (_∙ ap g (ε y)) (ap-∘ f g (η (g y)))
      ii = ap (λ - → ap g - ∙ ap g (ε y)) (τ (g y))
      iii = square1
    square3 : η (g (f (g y))) ∙ ap g (ε y) ≡ ap (g ∘ f ∘ g) (ε y) ∙ ap g (ε y)
    square3 = tr (λ - → - ∙ ap g (ε y) ≡ ap (g ∘ f ∘ g) (ε y) ∙ ap g (ε y))
                 (~-id-naturality (g ∘ f) η ⁻¹) square2
    square4 : η (g (f (g y))) ∙ ap g (ε y) ≡ ap (g ∘ f ∘ g) (ε y) ∙ η (g y)
    square4 = begin
      η (g (f (g y))) ∙ ap g (ε y)         ≡˘⟨ i   ⟩
      η (g (f (g y))) ∙ ap id (ap g (ε y)) ≡⟨ ii   ⟩
      ap (g ∘ f) (ap g (ε y)) ∙ η (g y)    ≡˘⟨ iii ⟩
      ap (g ∘ f ∘ g) (ε y) ∙ η (g y)       ∎
     where
      i = ap (η (g (f (g y))) ∙_) (ap-id (ap g (ε y)))
      ii = ∼-naturality (g ∘ f) id η
      iii = ap (_∙ η (g y)) (ap-∘ g (g ∘ f) (ε y))

isHae'⇒isHae : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
       → (f : A → B)
       → isHae' f → isHae f
isHae'⇒isHae f (g , η , ε , τ) =
  let (_ , _ , _ , ν) = isHae⇒isHae' g (f , ε , η , τ)
   in (g , η , ε , ν)

-- Helper
isHae⇒isQinv : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y)
           → isHae f → isQinv f
isHae⇒isQinv f (g , η , ε , τ) = g , ε , η

-- Theorem 4.2.3.
isQinv⇒isHae : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y)
                     → isQinv f → isHae f
isQinv⇒isHae f (g , ε , η) = g , η , ε' , τ
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
       (ε (f (g (f x))))⁻¹ ∙ (ap f (η (g (f x))) ∙ ε (f x)) ≡⟨⟩
       ε' (f x)                                             ∎
    where
     by-⁻¹-left∙ = ap (_∙ ap f (η x)) ((⁻¹-left∙ (ε (f (g (f x)))))⁻¹)
     by-∙assoc   = ∙-assoc ((ε (f (g (f x))))⁻¹)
     by-q        = ap ((ε (f (g (f x))))⁻¹ ∙_) (q ⁻¹)

-- Definition 4.2.4.
fib : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) → B → 𝒰 (𝒾 ⊔ 𝒿)
fib f y = Σ x ꞉ domain f , f x ≡ y

-- Helper for the next lemma
≡-comm : {A : 𝒰 𝒾} {x y : A}
       → (p q : x ≡ y) → (p ≡ q) ≡ (q ≡ p)
≡-comm p q = ua eqv
  where
    eqv : (p ≡ q) ≃ (q ≡ p)
    eqv = (_⁻¹) , invs⇒equivs (_⁻¹) ((_⁻¹) , ⁻¹-involutive , ⁻¹-involutive)

-- Lemma 4.2.5.
fib-≡-≃ : {𝒾 𝒿 : Level} {A : 𝒰 𝒾} {B : 𝒰 𝒿}
        → (f : A → B) (y : B)
          ((x , p) (x' , p') : fib f y)
        → ((x , p) ≡ (x' , p')) ≃ (Σ γ ꞉ (x ≡ x') , ap f γ ∙ p' ≡ p)
fib-≡-≃ f y (x , p) (x' , p') =
  tr (λ - → ((x , p) ≡ (x' , p')) ≃ -) ≡fams (≡-Σ-≃ _ _)
 where
  const-y = λ _ → y

  ∼fams : (λ γ → tr (λ - → f - ≡ y) γ p ≡ p') ∼ (λ γ → ap f γ ∙ p' ≡ p)
  ∼fams γ = begin
    (tr (λ - → f - ≡ y) γ p ≡ p')      ≡⟨ by-tr-γ⁻¹ γ ⟩
    (p ≡ tr (λ - → f - ≡ y) (γ ⁻¹) p') ≡⟨ ap (p ≡_) tr-lemma ⟩
    (p ≡ ap f γ ∙ p')                  ≡⟨ ≡-comm p (ap f γ ∙ p') ⟩
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
       ii = ap (λ - → (ap f (γ ⁻¹))⁻¹ ∙ p' ∙ -) (ap-const (γ ⁻¹) y)
       iii = ∙-assoc ((ap f (γ ⁻¹))⁻¹)
       iv = ap ((ap f (γ ⁻¹))⁻¹ ∙_) refl-right
       v = ap (_∙ p') (ap-⁻¹ f (γ ⁻¹))
       vi = ap (λ - → ap f - ∙ p') (⁻¹-involutive γ)

  ≡fams : (Σ (λ γ → tr (λ - → f - ≡ y) γ p ≡ p')) ≡ (Σ (λ γ → ap f γ ∙ p' ≡ p))
  ≡fams = ap Σ (funext ∼fams)


-- Theorem 4.2.6.
isHae⇒isContr-fib : {𝒾 𝒿 : Level} {A : 𝒰 𝒾} {B : 𝒰 𝒿}
                  → (f : A → B) → (isHae f) → (y : B)
                  → isContr (fib f y)
isHae⇒isContr-fib f (g , η , ε , τ) y = center , contraction
 where
  center = (g y , ε y)
  contraction : (xp : fib f y) → center ≡ xp
  contraction (x , p) = sufficient (γ , fγ∙p≡εγ)
   where
    sufficient : (Σ γ ꞉ g y ≡ x , ap f γ ∙ p ≡ ε y) → center ≡ (x , p)
    sufficient = ≃-→ (≃-sym (fib-≡-≃ f y center (x , p)))
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
      i    = ap (_∙ p) (ap-∙ f ((ap g p)⁻¹) (η x))
      ii   = ap (λ - → ap f ((ap g p)⁻¹) ∙ - ∙ p) (τ x)
      iii  = ∙-assoc (ap f ((ap g p)⁻¹))
      iv   = ap (λ - → ap f ((ap g p)⁻¹) ∙ (ε (f x) ∙ -)) ((ap-id p)⁻¹)
      v    = ap (ap f ((ap g p)⁻¹) ∙_) (∼-naturality (f ∘ g) id ε)
      vi   = ap (λ - → ap f - ∙ (ap (f ∘ g) p ∙ ε y)) (ap-⁻¹ g p)
      vii  = ap (_∙ (ap (f ∘ g) p ∙ ε y)) ((ap-∘ g f (p ⁻¹))⁻¹)
      viii = (∙-assoc (ap (f ∘ g) (p ⁻¹)))⁻¹
      ix   = ap (_∙ ε y) ((ap-∙ (f ∘ g) (p ⁻¹) p)⁻¹)
      x'   = ap (λ - → ap (f ∘ g) - ∙ ε y) (⁻¹-left∙ p)
      xi   = refl-left

-- Definition 4.2.7.
isLinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) → 𝒰 (𝒾 ⊔ 𝒿)
isLinv {𝒾} {𝒿} {A} {B} f = Σ g ꞉ (B → A) , (g ∘ f) ∼ id

isRinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) → 𝒰 (𝒾 ⊔ 𝒿)
isRinv {𝒾} {𝒿} {A} {B} f = Σ g ꞉ (B → A) , (f ∘ g) ∼ id

-- Lemma 4.2.8.
isQinv⇒isQinv-f∘─ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
         → (f : A → B)
         → isQinv f → (isQinv (λ (- : C → A) → f ∘ -))
isQinv⇒isQinv-f∘─ f (g , f∘g , g∘f) =
  ((g ∘_) , ∼₁ , ∼₂)
 where
  ∼₁ : (f ∘_) ∘ (g ∘_) ∼ id
  ∼₁ α = funext (λ x → f∘g (α x))
  ∼₂ : (g ∘_) ∘ (f ∘_) ∼ id
  ∼₂ β = funext (λ x → g∘f (β x))

isQinv⇒isQinv-─∘f : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
         → (f : A → B)
         → isQinv f → (isQinv (λ (- : B → C) → - ∘ f))
isQinv⇒isQinv-─∘f f (g , f∘g , g∘f) =
  ((_∘ g) , ∼₁ , ∼₂)
 where
  ∼₁ : (_∘ f) ∘ (_∘ g) ∼ id
  ∼₁ α = funext (λ x → ap α (g∘f x))
  ∼₂ : (_∘ g) ∘ (_∘ f) ∼ id
  ∼₂ β = funext (λ x → ap β (f∘g x))

-- Helper for the next Lemma
≃-preserves-contr : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
                  → A ≃ B
                  → isContr A
                  → isContr B
≃-preserves-contr {𝒾} {𝒿} {A} {B} equiv isContrA =
  ≃𝟙⇒isContr B i
  where
    i : B ≃ 𝟙
    i = ≃-trans (≃-sym equiv) (isContr⇒≃𝟙 A isContrA)

-- Lemma 4.2.9.
isQinv⇒isContr-isLinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
         → (f : A → B)
         → isQinv f → isContr (isLinv f)
isQinv⇒isContr-isLinv f isQinv-f =
  ≃-preserves-contr (≃-sym i) iv
 where
  i : isLinv f ≃ (Σ g ꞉ (codomain f → domain f) , g ∘ f ≡ id)
  i = map , invs⇒equivs map (map⁻¹ , ε , η)
   where
    map = λ (g , η) → (g , funext η)
    map⁻¹ = λ (g , p) → (g , happly p)
    ε = λ (g , p) → pair⁼ (refl g , ((≡-Π-uniq p)⁻¹))
    η = λ (g , η) → pair⁼ (refl g , (≡-Π-comp η))
  ii : isQinv (_∘ f)
  ii = isQinv⇒isQinv-─∘f f isQinv-f
  iii : isHae (_∘ f)
  iii = isQinv⇒isHae (_∘ f) ii
  iv : isContr (fib (_∘ f) id)
  iv  = isHae⇒isContr-fib (_∘ f) iii id

isQinv⇒isContr-isRinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
         → (f : A → B)
         → isQinv f → isContr (isRinv f)
isQinv⇒isContr-isRinv f isQinv-f =
  ≃-preserves-contr (≃-sym i) iv
 where
  i : isRinv f ≃ (Σ g ꞉ (codomain f → domain f) , f ∘ g ≡ id)
  i = map , invs⇒equivs map (map⁻¹ , ε , η)
   where
    map = λ (g , ε) → (g , funext ε)
    map⁻¹ = λ (g , p) → (g , happly p)
    ε = λ (g , p) → pair⁼ (refl g , ((≡-Π-uniq p)⁻¹))
    η = λ (g , ε) → pair⁼ (refl g , (≡-Π-comp ε))
  ii : isQinv (f ∘_)
  ii = isQinv⇒isQinv-f∘─ f isQinv-f
  iii : isHae (f ∘_)
  iii = isQinv⇒isHae (f ∘_) ii
  iv : isContr (fib (f ∘_) id)
  iv  = isHae⇒isContr-fib (f ∘_) iii id

-- Definition 4.2.10.
lcoh : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) ((g , η) : isLinv f) → 𝒰 (𝒾 ⊔ 𝒿)
lcoh f (g , η) = Σ ε ꞉ (f ∘ g ∼ id) , ((y : codomain f) → ap g (ε y) ≡ η (g y))

rcoh : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) ((g , ε) : isRinv f) → 𝒰 (𝒾 ⊔ 𝒿)
rcoh f (g , ε) = Σ η ꞉ (g ∘ f ∼ id) , ((x : domain f) → ap f (η x) ≡ ε (f x))

-- Helper for next lemmas
Π-distributes-≃ : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿} {Q : X → 𝒰 𝒿}
                → ((x : X) → P x ≃ Q x)
                → ((x : X) → P x) ≃ ((x : X) → Q x)
Π-distributes-≃ h = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = λ f → (λ x → (≃-→ (h x)) (f x))
  map⁻¹ = λ g → (λ x → (≃-← (h x) (g x)))
  ε = λ g → funext (λ x → ≃-ε (h x) (g x))
  η = λ f → funext (λ x → ≃-η (h x) (f x))

-- Lemma 4.2.11.
lcoh≃ : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
      → (f : A → B) ((g , η) : isLinv f)
      → lcoh f (g , η) ≃
         ((y : B) → Id (fib g (g y)) (f (g y) , η (g y)) (y , refl (g y)))
lcoh≃ f (g , η) = ≃-trans (≃-trans i ii') iii'
 where
  i : lcoh f (g , η) ≃
       ((y : codomain f) → (Σ εy ꞉ (f (g y) ≡ y) , (ap g εy ≡ η (g y))))
  i = ≃-sym ΠΣ-comm
  ii : (y : codomain f)
     → (Σ εy ꞉ (f (g y) ≡ y) , (ap g εy ≡ η (g y)))
        ≡ (Σ εy ꞉ (f (g y) ≡ y) , (ap g εy ∙ refl (g y) ≡ η (g y)))
  ii y = ap Σ (funext (λ εy → ap (λ - → - ≡ η (g y)) (refl-right ⁻¹)))
  ii' = Π-distributes-≃ (λ y → idtoeqv (ii y))
  iii : (y : codomain f)
      → (Σ εy ꞉ (f (g y) ≡ y) , (ap g εy ∙ refl (g y) ≡ η (g y)))
        ≃ Id (fib g (g y)) (f (g y) , η (g y)) (y , refl (g y))
  iii y = ≃-sym (fib-≡-≃ g (g y) (f (g y) , η (g y)) (y , refl (g y)))
  iii' = Π-distributes-≃ iii

rcoh≃ : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
      → (f : A → B) ((g , ε) : isRinv f)
      → rcoh f (g , ε) ≃
         ((x : A) → Id (fib f (f x)) (g (f x) , ε (f x)) (x , refl (f x)))
rcoh≃ f (g , ε) = ≃-trans (≃-trans i ii') iii'
 where
  i : rcoh f (g , ε) ≃
       ((x : domain f) → (Σ ηx ꞉ (g (f x) ≡ x) , (ap f ηx ≡ ε (f x))))
  i = ≃-sym ΠΣ-comm
  ii : (x : domain f)
     → (Σ ηx ꞉ (g (f x) ≡ x) , (ap f ηx ≡ ε (f x)))
        ≡ (Σ ηx ꞉ (g (f x) ≡ x) , (ap f ηx ∙ refl (f x) ≡ ε (f x)))
  ii x = ap Σ (funext (λ ηx → ap (λ - → - ≡ ε (f x)) (refl-right ⁻¹)))
  ii' = Π-distributes-≃ (λ x → idtoeqv (ii x))
  iii : (x : domain f)
      → (Σ ηx ꞉ (g (f x) ≡ x) , (ap f ηx ∙ refl (f x) ≡ ε (f x)))
        ≃ Id (fib f (f x)) (g (f x) , ε (f x)) (x , refl (f x))
  iii x = ≃-sym (fib-≡-≃ f (f x) (g (f x) , ε (f x)) (x , refl (f x)))
  iii' = Π-distributes-≃ iii

-- Lemma 4.2.12.
isHae-isRinv⇒isContr-rcoh : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
    → (f : A → B) → isHae f → ((g , ε) : isRinv f)
    → isContr (rcoh f (g , ε))
isHae-isRinv⇒isContr-rcoh f haef (g , ε) =
  ≃-preserves-contr (≃-sym (rcoh≃ f (g , ε))) Πpath-space-isContr
 where
  path-space-isContr : (x : domain f) →
    isContr (Id (fib f (f x)) (g (f x) , ε (f x)) (x , refl (f x)))
  path-space-isContr x = isProp⇒isContr-≡
    fib-isProp (g (f x) , ε (f x)) (x , refl (f x))
   where
    fib-isContr = isHae⇒isContr-fib f haef (f x)
    fib-isProp = pr₂ (isContr⇒isPointedProp (fib f (f x)) fib-isContr)
  Πpath-space-isContr = isContr-Π path-space-isContr

-- Helpers for the next theorem
Σ-weak-comm : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
            → {P : A → B → 𝒰 𝓀}
            → (Σ a ꞉ A , (Σ b ꞉ B , P a b))
               ≃ (Σ b ꞉ B , (Σ a ꞉ A , P a b))
Σ-weak-comm = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = λ (a , b , c) → (b , a , c)
  map⁻¹ = λ (b , a , c) → (a , b , c)
  ε = λ - → refl -
  η = λ - → refl -

≃-sections-implies-≃-Σ : {A : 𝒰 𝒾}
            → {P : A → 𝒰 𝒿}
            → {Q : A → 𝒰 𝓀}
            → ((x : A) → P x ≃ Q x)
            → (Σ a ꞉ A , P a) ≃ (Σ a ꞉ A , Q a)
≃-sections-implies-≃-Σ equiv = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = λ (a , pa) → (a , ≃-→ (equiv a) pa)
  map⁻¹ = λ (a , qa) → (a , ≃-← (equiv a) qa)
  ε = λ (a , qa) → pair⁼(refl a , ≃-ε (equiv a) qa)
  η = λ (a , pa) → pair⁼(refl a , ≃-η (equiv a) pa)

Σ-preserves-contr : {A : 𝒰 𝒾}
                  → {P : A → 𝒰 𝒿}
                  → isContr A
                  → ((a : A) → isContr (P a))
                  → isContr (Σ a ꞉ A , P a)
Σ-preserves-contr {𝒾} {𝒿} {A} {P} isContrA f =
  ≃-preserves-contr (≃-sym ΣAP≃A) isContrA
 where
  ΣAP≃A = isContr-Σ⇒base P f

-- Theorem 4.2.13.
isProp-isHae : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
    → (f : A → B)
    → isProp (isHae f)
isProp-isHae f =
  point→isContr-implies-isProp iv
 where
  i : isHae f ≃ (Σ g ꞉ (codomain f → domain f)
                , Σ ε ꞉ f ∘ g ∼ id
                , Σ η ꞉ g ∘ f ∼ id
                , ((x : domain f) → ap f (η x) ≡ ε (f x)))
  i = ≃-sections-implies-≃-Σ (λ g → Σ-weak-comm)
  ii : (Σ g ꞉ (codomain f → domain f)
      , Σ ε ꞉ f ∘ g ∼ id
      , Σ η ꞉ g ∘ f ∼ id
      , ((x : domain f) → ap f (η x) ≡ ε (f x)))
        ≃ (Σ u ꞉ isRinv f , rcoh f (pr₁ u , pr₂ u))
  ii = Σ-assoc (λ z → Σ (λ η → (x : domain f) → ap f (η x) ≡ pr₂ z (f x)))
  iii : isHae f → isContr (Σ u ꞉ isRinv f , rcoh f (pr₁ u , pr₂ u))
  iii haef = Σ-preserves-contr isRinv-isContr rcoh-isContr
   where
    isRinv-isContr : isContr (isRinv f)
    isRinv-isContr = isQinv⇒isContr-isRinv f (isHae⇒isQinv f haef)
    rcoh-isContr : ((g , ε) : isRinv f) → isContr (rcoh f (g , ε))
    rcoh-isContr (g , ε) =
      isHae-isRinv⇒isContr-rcoh f haef (g , ε)
  iv : isHae f → isContr (isHae f)
  iv haef = ≃-preserves-contr (≃-sym (≃-trans i ii)) (iii haef)
```

## 4.3 Bi-invertible maps

```agda
-- Definition 4.3.1.
isBiinv : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 (𝒾 ⊔ 𝒿)
isBiinv f = isRinv f × isLinv f

-- Helper for the next theorem
×-preserves-contr : {A : 𝒰 𝒾} → {B : 𝒰 𝒿}
                  → isContr A
                  → isContr B
                  → isContr (A × B)
×-preserves-contr isContr-A isContr-B =
  Σ-preserves-contr isContr-A (λ - → isContr-B)

-- Theorem 4.3.2.
isProp-isBiinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
             → (f : A → B) → isProp (isBiinv f)
isProp-isBiinv f =
  point→isContr-implies-isProp v
 where
  v : isBiinv f → isContr (isBiinv f)
  v isBiinv-f = ×-preserves-contr isRinv-isContr isLinv-isContr
   where
    isQinv-f : isQinv f
    isQinv-f = equivs⇒invs f isBiinv-f
    isLinv-isContr = isQinv⇒isContr-isLinv f isQinv-f
    isRinv-isContr = isQinv⇒isContr-isRinv f isQinv-f

isProp-isEquiv : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
             → (f : A → B) → isProp (isEquiv f)
isProp-isEquiv = isProp-isBiinv

-- Corollary 4.3.3.
isHae⇒isBiinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
              → (f : A → B)
              → isHae f → isBiinv f
isHae⇒isBiinv f haef = invs⇒equivs f (isHae⇒isQinv f haef)
-- TODO
```

## 4.4 Contractible fibers

```agda
-- Definition 4.1.1.
isContrMap : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → B) → 𝒰 (𝒾 ⊔ 𝒿)
isContrMap f = (y : codomain f) → isContr (fib f y)

-- Theorem 4.4.3.
isContrMap⇒isHae : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
             → (f : A → B)
             → isContrMap f → isHae f
isContrMap⇒isHae f P = g , pr₁ rcohf , ε , pr₂ rcohf
 where
  g = λ y → pr₁ (pr₁ (P y))
  ε = λ y → pr₂ (pr₁ (P y))
  rcohf : rcoh f (g , ε)
  rcohf = ≃-← (rcoh≃ f (g , ε))
           (λ x → (pr₂ (P (f x)) (g (f x) , ε (f x)))⁻¹
                   ∙ (pr₂ (P (f x)) (x , refl (f x))))

-- Lemma 4.4.4.
isProp-isContrMap : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
                  → (f : A → B)
                  → isProp (isContrMap f)
isProp-isContrMap f =
  isProp-Π (λ y → isProp-isContr (fib f y))
```

## 4.6 Surjections and embeddings

```agda
isSurjec : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
         → (f : A → B)
         → 𝒰 (𝒾 ⊔ 𝒿)
isSurjec f = (b : codomain f) → ∥ fib f b ∥

isEmbedding : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
            → (f : A → B)
            → 𝒰 (𝒾 ⊔ 𝒿)
isEmbedding f = (x y : domain f) → isEquiv (ap f {x} {y})

isInjective : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
            → (f : A → B)
            → 𝒰 (𝒾 ⊔ 𝒿)
isInjective f = (x y : domain f) → (f x ≡ f y) → x ≡ y

isEmbedding⇒isInjective :
         {A : 𝒰 𝒾} {B : 𝒰 𝒿}
       → (f : A → B)
       → isEmbedding f
       → isInjective f
isEmbedding⇒isInjective f e x y = ≃-← (ap f , e x y)

isSet-isInjective⇒isEmbedding :
             {A : 𝒰 𝒾} {B : 𝒰 𝒾}
           → isSet A → isSet B
           → (f : A → B)
           → isInjective f
           → isEmbedding f
isSet-isInjective⇒isEmbedding p q f i x y =
  pr₂ (isProp-areLogEq⇒Eq (x ≡ y) (f x ≡ f y) p q (ap f) (i x y))

-- Theorem 4.6.3.
isEquiv⇒isSurj-isEmbedding :
             {A : 𝒰 𝒾} {B : 𝒰 𝒾}
           → (f : A → B)
           → isEquiv f
           → (isEmbedding f × isSurjec f)
isEquiv⇒isSurj-isEmbedding f e =
  (isEquiv⇒isEquiv-ap f e , fibEl)
 where
  fibEl = λ b → ∣ pr₁ (isHae⇒isContr-fib f
                  (isQinv⇒isHae f (equivs⇒invs f e)) b) ∣

tr-fx≡x : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) {a b : A} {y : B}
          (r : a ≡ b) (p : f a ≡ y) (q : f b ≡ y)
         → ap f r ≡ p ∙ (q ⁻¹) → tr (λ x → f x ≡ y) r p ≡ q
tr-fx≡x f (refl a) (refl _) q lem = begin
  refl (f a)              ≡˘⟨ ⁻¹-left∙ q ⟩
  q ⁻¹ ∙ q                ≡˘⟨ refl-left ⟩
  refl (f a) ∙ (q ⁻¹ ∙ q) ≡˘⟨ ∙-assoc (refl (f a)) ⟩
  refl (f a) ∙ q ⁻¹ ∙ q   ≡˘⟨ ap (_∙ q) lem ⟩
  refl (f a) ∙ q          ≡⟨ refl-left ⟩
  q                       ∎

isSurj-isEmbedding⇒isEquiv :
             {A : 𝒰 𝒾} {B : 𝒰 𝒾}
           → (f : A → B)
           → isSurjec f
           → isEmbedding f
           → isEquiv f
isSurj-isEmbedding⇒isEquiv f s e =
  invs⇒equivs f (isHae⇒isQinv f (isContrMap⇒isHae f isContrMap-f))
 where
  isContrMap-f : (y : _) → isContr (fib f y)
  isContrMap-f y = ∥∥-rec (fib f y) (isContr (fib f y))
                    (isProp-isContr (fib f y))
                    (λ - → isPointedProp⇒isContr _ (- , fib-isProp)) (s y)
   where
    fib-isProp : isProp (fib f y)
    fib-isProp (a , p) (b , q) =
      pair⁼(r , tr-fx≡x f r p q (≃-ε (ap f , e a b) _))
     where
      r = ≃-← (ap f , e a b) (p ∙ (q ⁻¹))

isProp-isSurjec : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
                → (f : A → B)
                → isProp (isSurjec f)
isProp-isSurjec f = isProp-Π (λ - → ∥∥-isProp)
```
