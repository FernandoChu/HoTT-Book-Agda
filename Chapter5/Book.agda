{-# OPTIONS --without-K --exact-split --safe --auto-inline --no-import-sorts #-}

module Chapter5.Book where

open import Chapter4.Exercises public

---------------------------------------------------------------------------------

-- 5.1 Introduction to inductive types

-- Theorem 5.1.1
ℕ-uniqueness : funext →
               (E : ℕ → 𝒰 𝒾)
               (f g : (x : ℕ) → E x)
               (ez : E 0)
               (eₛ : (n : ℕ) → (E n) → (E (succ n)))
             → (f 0 ≡ ez) → (g 0 ≡ ez)
             → ((n : ℕ) → f (succ n) ≡ eₛ n (f n))
             → ((n : ℕ) → g (succ n) ≡ eₛ n (g n))
             → f ≡ g
ℕ-uniqueness fe E f g ez eₛ f0 g0 fs gs
  = (pr₁ (pr₁ (fe f g))) f∼g
    where
      f∼g : f ∼ g
      f∼g 0 = f0 ∙ (g0 ⁻¹)
      f∼g (succ n) = begin
        f (succ n) ≡⟨ fs n ⟩
        eₛ n (f n) ≡⟨ ap (λ - → eₛ n -) (f∼g n) ⟩
        eₛ n (g n) ≡˘⟨ gs n ⟩
        g (succ n) ∎

---------------------------------------------------------------------------------

-- 5.2 Uniqueness of inductive types

---------------------------------------------------------------------------------

-- 5.3 W-types

data 𝕎 (A : 𝒰 𝒾) (B : A → 𝒰 𝒿) : 𝒰 (𝒾 ⊔ 𝒿) where
  sup : (x : A) (f : B x → 𝕎 A B) → 𝕎 A B

N𝕎 : 𝒰₀
N𝕎 = 𝕎 𝟚 f
  where
    f : 𝟚 → 𝒰₀
    f ₀ = 𝟘
    f ₁ = 𝟙

List : (A : 𝒰 𝒾) → 𝒰 𝒾
List A = 𝕎 (𝟙 ⊎ A) f
  where
    f : 𝟙 ⊎ A → 𝒰₀
    f (inl ⋆) = 𝟘
    f (inr a) = 𝟙

0𝕎 1𝕎 : N𝕎
0𝕎 = sup ₀ (λ x → !𝟘 N𝕎 x)
1𝕎 = sup ₁ (λ x → 0𝕎)

succ𝕎 : N𝕎 → N𝕎
succ𝕎 n = sup ₁ (λ x → n)

𝕎-induction : (A : 𝒰 𝒾) (B : A → 𝒰 𝒿) (E : 𝕎 A B → 𝒰 𝓀)
              (e : (a : A) (f : B a → 𝕎 A B)
                   (g : (b : B a) → E (f b)) → E (sup a f))
            → ((w : 𝕎 A B) → E w)
𝕎-induction A B E e (sup x f) = e x f (λ b → 𝕎-induction A B E e (f b))

double𝕎 : N𝕎 → N𝕎
double𝕎 (sup ₀ α) = 0𝕎
double𝕎 (sup ₁ α) = succ𝕎 (succ𝕎 (α ⋆))

double𝕎-1𝕎 : double𝕎 1𝕎 ≡ succ𝕎 (succ𝕎 0𝕎)
double𝕎-1𝕎 = refl (double𝕎 1𝕎)

---------------------------------------------------------------------------------

-- 5.4 Inductive types are initial algebras

-- Definition 5.4.1
ℕAlg : {𝒾 : Level} → 𝒰 (𝒾 ⁺)
ℕAlg {𝒾} = Σ C ꞉ 𝒰 𝒾 , C × (C → C)

-- Definition 5.4.2
ℕHom : {𝒾 : Level} (C D : ℕAlg) → 𝒰 𝒾
ℕHom (C , c₀ , cₛ) (D , d₀ , dₛ) =
  Σ h ꞉ (C → D) , (h c₀ ≡ d₀) × ((c : C) → h (cₛ c) ≡ dₛ (h c))

-- Lemmas needed for 5.4.4

∘-ℕHom : {𝒾 : Level}
         (C D E : ℕAlg {𝒾})
         (f : ℕHom C D) (g : ℕHom D E)
       → ℕHom C E
∘-ℕHom (C , c₀ , cₛ) (D , d₀ , dₛ) (E , e₀ , eₛ)
  (f , fc₀ , fc) (g , gd₀ , gd) =
    (g ∘ f , p , q)
  where
    p : g (f c₀) ≡ e₀
    p = g (f c₀) ≡⟨ ap g fc₀ ⟩
        g d₀     ≡⟨ gd₀ ⟩
        e₀       ∎
    q : (c : C) → g (f (cₛ c)) ≡ eₛ (g (f c))
    q c = g (f (cₛ c)) ≡⟨ ap g (fc c) ⟩
          g (dₛ (f c)) ≡⟨ gd (f c) ⟩
          eₛ (g (f c)) ∎

id-ℕHom : {𝒾 : Level}
          (C : ℕAlg {𝒾})
        → ℕHom C C
id-ℕHom (C , c₀ , cₛ) =
  (id , refl c₀ , λ - → refl (cₛ -))

-- Definition 5.4.3
isHinit-ℕ : {𝒾 : Level} (I : ℕAlg) → 𝒰 (𝒾 ⁺)
isHinit-ℕ I = (C : ℕAlg) → isContr (ℕHom I C)

-- Theorem 5.4.4
isHinit-ℕ-isProp : {𝒾 : Level}
                 → (is-univalent 𝒾)
                 → (I J : ℕAlg {𝒾})
                 → (isHinit-ℕ I) → (isHinit-ℕ J)
                 → I ≡ J
isHinit-ℕ-isProp ua I@(cI , i₀ , iₛ) J@(cJ , j₀ , jₛ) fI gJ =
 pair⁼ (cI≡cJ , missing)
 where
  F : ℕHom I J
  F = pr₁ (fI J)
  G : ℕHom J I
  G = pr₁ (gJ I)
  f : pr₁ I → pr₁ J
  f = pr₁ F
  g : pr₁ J → pr₁ I
  g = pr₁ G

  g∘f≡id : g ∘ f ≡ id
  g∘f≡id = ap pr₁ (endoI-isProp (∘-ℕHom I J I F G) (id-ℕHom I))
   where
    endoI-isProp : isProp (ℕHom I I)
    endoI-isProp = pr₂ (contr-are-pointed-props (ℕHom I I) (fI I))

  f∘g≡id : f ∘ g ≡ id
  f∘g≡id = ap pr₁ (endoJ-isProp (∘-ℕHom J I J G F) (id-ℕHom J))
   where
    endoJ-isProp : isProp (ℕHom J J)
    endoJ-isProp = pr₂ (contr-are-pointed-props (ℕHom J J) (gJ J))

  cI≡cJ : cI ≡ cJ
  cI≡cJ = Eq→Id ua (pr₁ I) (pr₁ J) (f , invs-are-equivs f q-qinv-f)
   where
    q-qinv-f : qinv f
    q-qinv-f = (g , happly (f ∘ g) id f∘g≡id , happly (g ∘ f) id g∘f≡id)

  missing : tr (λ C → C × (C → C)) cI≡cJ (i₀ , iₛ) ≡
              (j₀ , jₛ)
  missing = _

  related? : (cI × (cI → cI)) → (cJ × (cJ → cJ))
  related? = tr (λ C → C × (C → C)) cI≡cJ
