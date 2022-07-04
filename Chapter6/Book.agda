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

module Circle1 (circle : CircleExists) where
 open module circle-data1 = Circle circle public
 module CircleInd1 (𝕊¹-ind-comp : {𝒾 : Level}
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
  --   contrFib y@(b , l) = fibφ , fibeq
  --    where
  --     f = 𝕊¹-rec A b l
  --     eqf = pair⁼(refl b , 𝕊¹-rec-comp A b l)
  --     fibφ = (f , eqf)

  --     fibeq : ((g , eqg) : fib φ (b , l)) → (f , eqf) ≡ (g , eqg)
  --     fibeq (g , eqg) = pair⁼(f≡g , eqf≡eqg)
  --      where
  --       f≡g-lemma : tr (λ x → x ≡ x) (ap pr₁ eqg ⁻¹) (ap f loop) ≡ ap g loop
  --       f≡g-lemma = begin
  --         tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) (ap f loop)              ≡⟨ i ⟩
  --         tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) l                        ≡⟨ ii ⟩
  --         tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
  --           (tr (λ x → x ≡ x) (pr₁ (pair⁼⁻¹ eqg)) (ap g loop))       ≡⟨ iii ⟩
  --         tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
  --           (tr (λ x → x ≡ x) (ap pr₁ eqg) (ap g loop))              ≡⟨ iv ⟩
  --         tr (λ x → x ≡ x) (ap pr₁ eqg ∙ (ap pr₁ eqg)⁻¹) (ap g loop) ≡⟨ v ⟩
  --         ap g loop ∎
  --        where
  --         i = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) -) (𝕊¹-rec-comp A b l)
  --         ii = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹) -)
  --                  ((pr₂ (pair⁼⁻¹ eqg))⁻¹)
  --         Σ-lemma : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {w₁ w₂ : Σ B} (p : w₁ ≡ w₂)
  --                 → pr₁ (pair⁼⁻¹ p) ≡ ap pr₁ p
  --         Σ-lemma (refl _) = refl _
  --         iii = ap (λ - → tr (λ x → x ≡ x) ((ap pr₁ eqg)⁻¹)
  --                   (tr (λ x → x ≡ x) - (ap g loop))) (Σ-lemma eqg)
  --         iv = happly (tr-∘ (λ x → x ≡ x) (ap pr₁ eqg) ((ap pr₁ eqg)⁻¹))
  --                      (ap g loop)
  --         v = ap (λ - → tr (λ x → x ≡ x) - (ap g loop)) (⁻¹-right∙ (ap pr₁ eqg))
  --       f≡g = funext fe1 (𝕊¹-ind-uniq f g ((ap pr₁ eqg)⁻¹) f≡g-lemma)
  --       eqf≡eqg : tr (λ x → φ x ≡ b , l) f≡g eqf ≡ eqg
  --       eqf≡eqg = begin
  --         tr (λ x → φ x ≡ b , l) f≡g eqf              ≡⟨ i ⟩
  --         (ap φ f≡g)⁻¹ ∙ eqf ∙ (ap (λ _ → b , l) f≡g) ≡⟨ ii ⟩
  --         (ap φ f≡g)⁻¹ ∙ eqf ∙ refl _                 ≡⟨ iii ⟩
  --         (ap φ f≡g)⁻¹ ∙ (eqf ∙ refl _)               ≡⟨ iv ⟩
  --         (ap φ f≡g)⁻¹ ∙ eqf                          ≡⟨ v eqf eqg f≡g ⟩
  --         eqg ∎
  --        where
  --         i = tr-fx≡gx φ (λ _ → (b , l)) f≡g eqf
  --         ii = ap ((ap φ f≡g)⁻¹ ∙ eqf ∙_) (ap-const f≡g (b , l))
  --         iii = ∙-assoc ((ap φ f≡g)⁻¹)
  --         iv = ap ((ap φ f≡g)⁻¹ ∙_) refl-right
  --         v : {f g : 𝕊¹ → A} (eqf : φ f ≡ b , l) (eqg : φ g ≡ b , l) (p : f ≡ g) → (ap φ p)⁻¹ ∙ eqf ≡ eqg
  --         v eqh eqg (refl h) = refl-left ∙ _

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

module Circle2 (circle : CircleExists) where
 open module circle-data2 = Circle1 circle public
 module _ (𝕊¹-ind-comp : {𝒾 : Level}
                         (P : 𝕊¹ → 𝒰 𝒾)
                       → (b : P base)
                       → (l : tr P loop b ≡ b)
                       → (apd (𝕊¹-ind P b l) loop ≡ l))
          where
  open module circle-ind2 = CircleInd1 𝕊¹-ind-comp

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

---------------------------------------------------------------------------------

-- 6.5 Suspensions

module Suspensions1 (suspension : SuspensionsExist) where
 open module suspension-data1 = Suspension suspension public
 module suspension-ind1
     (𝝨-rec-comp : {𝒾 𝒿 : Level}
                   (A : 𝒰 𝒾) (B : 𝒰 𝒿)
                 → (n s : B)
                 → (m : A → (n ≡ s))
                 → ((a : A) → ap (𝝨-rec A B n s m) (merid A a) ≡ (m a)))
     (𝝨-ind-comp : {𝒾 𝒿 : Level}
            (A : 𝒰 𝒾) (P : 𝝨 A → 𝒰 𝒿)
          → (n : P (N A)) → (s : P (S A))
          → (m : (a : A) → tr P (merid A a) n ≡ s)
          → ((a : A) → (apd (𝝨-ind A P n s m) (merid A a) ≡ m a)))
          where

  module Circle3 (circle : CircleExists) where
   open module circle-data3 = Circle2 circle public
   module _ (𝕊¹-ind-comp : {𝒾 : Level}
                           (P : 𝕊¹ → 𝒰 𝒾)
                         → (b : P base)
                         → (l : tr P loop b ≡ b)
                         → (apd (𝕊¹-ind P b l) loop ≡ l))
            where
    open module circle-ind3 = circle-ind2 𝕊¹-ind-comp

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
            merid 𝟚 ₀ ∙ (refl (S 𝟚))                      ≡⟨ viii ⟩
            merid 𝟚 ₀ ∎
           where
            i    = ap (λ - → (-)⁻¹ ∙ merid 𝟚 ₀) (ap-∘ f g (merid 𝟚 ₀))
            ii   = ap (λ - → (ap g -)⁻¹ ∙ merid 𝟚 ₀)
                       (𝝨-rec-comp 𝟚 𝕊¹ base base
                        (𝟚-rec (base ≡ base) loop (refl base)) ₀)
            iii  = ap (λ - → (-)⁻¹ ∙ merid 𝟚 ₁)
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
  Map*' : has-funext 𝒾 𝒿
        → (A : 𝒰 𝒾) → ((B , b₀) : 𝒰∙ 𝒿)
        → Map* (A ₊) (B , b₀) ≃ (A → B)
  Map*' fe A (B , b₀) = map , invs-are-equivs map (map⁻¹ , ε , η)
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
