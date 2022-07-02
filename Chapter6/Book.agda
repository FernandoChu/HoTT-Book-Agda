module Chapter6.Book where

open import Chapter6.HITs public

---------------------------------------------------------------------------------

-- 6.1 Introduction

-- Workaround: Since HIT's are not available in agda, I'm implementing
-- them in another module. I need two nested modules to claim they exist
-- and have the appropriate computing rules (for the paths).
-- They compute as they should in the points.

---------------------------------------------------------------------------------

-- 6.2 Induction principles and dependent paths

module _ (circle : CircleExists) where
 open module circle-data = Circle circle
 module _ (𝕊¹-ind-comp : {𝒾 : Level}
                         (P : 𝕊¹ → 𝒰 𝒾)
                       → (b : P base)
                       → (l : tr P loop b ≡ b)
                       → (apd (𝕊¹-ind P b l) loop ≡ l))
          where

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
        → is-univalent 𝒾
        → has-funext lzero 𝒾
        → has-funext 𝒾 𝒾
        → has-funext 𝒾 (𝒾 ⁺)
        → (𝕊¹ → A) ≃ (Σ x ꞉ A , x ≡ x)
  𝕊¹→-≃ {𝒾} {A} u fe1 fe2 fe3 =
    φ , ishae→biinv φ (contrMap→hae u fe2 fe3 φ contrFib)
   where
    φ : (𝕊¹ → A) → (Σ x ꞉ A , x ≡ x)
    φ g = g base , ap g loop

    contrFib : (y : codomain φ) → isContr (fib φ y)
    contrFib y@(b , l) = fibφ , fibeq
     where
      f = 𝕊¹-rec A b l
      eqf = pair⁼(refl b , 𝕊¹-rec-comp A b l)
      fibφ = (f , eqf)

      fibeq : ((g , eqg) : fib φ (b , l)) → (f , eqf) ≡ (g , eqg)
      fibeq (g , eqg) = pair⁼(f≡g , eqf≡eqg)
       where
        f≡g-lemma : tr (λ x → x ≡ x) (ap pr₁ eqg ⁻¹) (ap f loop) ≡ ap g loop
        f≡g-lemma = begin
          tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) (ap f loop)              ≡⟨ i ⟩
          tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) l                        ≡⟨ ii ⟩
          tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
            (tr (λ x → x ≡ x) (pr₁ (pair⁼⁻¹ eqg)) (ap g loop))       ≡⟨ iii ⟩
          tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
            (tr (λ x → x ≡ x) (ap pr₁ eqg) (ap g loop))              ≡⟨ iv ⟩
          tr (λ x → x ≡ x) (ap pr₁ eqg ∙ (ap pr₁ eqg)⁻¹) (ap g loop) ≡⟨ v ⟩
          ap g loop ∎
         where
          i = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) -) (𝕊¹-rec-comp A b l)
          ii = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) -)
                   ((pr₂ (pair⁼⁻¹ eqg))⁻¹)
          Σ-lemma : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {w₁ w₂ : Σ B} (p : w₁ ≡ w₂)
                  → pr₁ (pair⁼⁻¹ p) ≡ ap pr₁ p
          Σ-lemma (refl _) = refl _
          iii = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
                    (tr (λ x → x ≡ x) - (ap g loop))) (Σ-lemma eqg)
          iv = happly (tr-∘ (λ x → x ≡ x) (ap pr₁ eqg) ((ap pr₁ eqg)⁻¹))
                       (ap g loop)
          v = ap (λ - → tr (λ x → x ≡ x) - (ap g loop)) (⁻¹-right∙ (ap pr₁ eqg))
        f≡g = funext fe1 (𝕊¹-ind-uniq f g ((ap pr₁ eqg)⁻¹) f≡g-lemma)
        eqf≡eqg : tr (λ x → φ x ≡ b , l) f≡g eqf ≡ eqg
        eqf≡eqg = begin
          tr (λ x → φ x ≡ b , l) f≡g eqf              ≡⟨ i ⟩
          (ap φ f≡g)⁻¹ ∙ eqf ∙ (ap (λ _ → b , l) f≡g) ≡⟨ ii ⟩
          (ap φ f≡g)⁻¹ ∙ eqf ∙ refl _                 ≡⟨ iii ⟩
          (ap φ f≡g)⁻¹ ∙ (eqf ∙ refl _)               ≡⟨ iv ⟩
          (ap φ f≡g)⁻¹ ∙ eqf                          ≡⟨ v eqf eqg f≡g ⟩
          eqg ∎
         where
          i = tr-fx≡gx φ (λ _ → (b , l)) f≡g eqf
          ap-lemma : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {a₁ a₂ : A}
                     (p : a₁ ≡ a₂) (c : B)
                   → ap (λ _ → c) p ≡ refl c
          ap-lemma (refl _) c = refl _
          ii = ap ((ap φ f≡g)⁻¹ ∙ eqf ∙_) (ap-lemma f≡g (b , l))
          iii = ∙-assoc ((ap φ f≡g)⁻¹)
          iv = ap ((ap φ f≡g)⁻¹ ∙_) refl-right
          v : {f g : 𝕊¹ → A} (eqf : φ f ≡ b , l) (eqg : φ g ≡ b , l) (p : f ≡ g) → (ap φ p)⁻¹ ∙ eqf ≡ eqg
          v eqh eqg (refl h) = refl-left ∙ _

---------------------------------------------------------------------------------

-- 6.3 The interval

module _ (interval : IntervalExists) where
 open module interval-data = Interval interval
 module _ (𝕀-rec-comp : {𝒾 : Level}
                        (B : 𝒰 𝒾)
                      → (b₀ b₁ : B)
                      → (s : b₀ ≡ b₁)
                      → (ap (𝕀-rec B b₀ b₁ s) seg ≡ s))
          (𝕀-ind-comp : {𝒾 : Level}
                        (P : 𝕀 → 𝒰 𝒾)
                      → (b₀ : P 0ᵢ)
                      → (b₁ : P 1ᵢ)
                      → (s : tr P seg b₀ ≡ b₁)
                      → (apd (𝕀-ind P b₀ b₁ s) seg ≡ s))
          where

  𝕀-isContr : isContr 𝕀
  𝕀-isContr = (1ᵢ , λ x → (contr x)⁻¹)
   where
    contr : (x : 𝕀) → (x ≡ 1ᵢ)
    contr = 𝕀-ind (λ x → x ≡ 1ᵢ) seg (refl 1ᵢ) treq
     where
      treq : tr (λ x → x ≡ 1ᵢ) seg seg ≡ refl 1ᵢ
      treq = (trHom-c 1ᵢ seg seg) ∙ (⁻¹-left∙ seg)

---------------------------------------------------------------------------------

-- 6.4 Circles and spheres

