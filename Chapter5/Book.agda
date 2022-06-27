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
ℕAlg : (𝒾 : Level) → 𝒰 (𝒾 ⁺)
ℕAlg 𝒾 = Σ C ꞉ 𝒰 𝒾 , C × (C → C)

-- Definition 5.4.2
ℕHom : (𝒾 j : Level) (C : ℕAlg 𝒾) (D : ℕAlg 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
ℕHom 𝒾 𝒿 (C , c₀ , cₛ) (D , d₀ , dₛ) =
  Σ h ꞉ (C → D) , (h c₀ ≡ d₀) × ((c : C) → h (cₛ c) ≡ dₛ (h c))

-- Lemmas needed for 5.4.4

∘-ℕHom : {𝒾 𝒿 𝓀 : Level}
         (C : ℕAlg 𝒾)
         (D : ℕAlg 𝒿)
         (E : ℕAlg 𝓀)
         (f : ℕHom 𝒾 𝒿 C D) (g : ℕHom 𝒿 𝓀 D E)
       → ℕHom 𝒾 𝓀 C E
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
          (C : ℕAlg 𝒾)
        → ℕHom 𝒾 𝒾 C C
id-ℕHom (C , c₀ , cₛ) =
  (id , refl c₀ , λ - → refl (cₛ -))

-- Definition 5.4.3
isHinit-ℕ : (𝒾 : Level) (I : ℕAlg 𝒾) → 𝒰 (𝒾 ⁺)
isHinit-ℕ 𝒾 I = (C : ℕAlg 𝒾) → isContr (ℕHom 𝒾 𝒾 I C)

d : (𝒾 : Level) → ℕAlg 𝒾 → 𝒰 (𝒾 ⁺)
d 𝒾 = isHinit-ℕ 𝒾

-- Theorem 5.4.4
isHinit-ℕ-isProp : (𝒾 𝒿 : Level)
                 → (is-univalent 𝒾)
                 → funext {𝒾} {𝒾}
                 → funext {𝒾 ⁺} {𝒾}
                 → funext {𝒾 ⁺} {𝒾 ⁺}
                 → (I J : ℕAlg 𝒾)
                 → (isHinit-ℕ 𝒾 I) → (isHinit-ℕ 𝒾 J)
                 → I ≡ J
isHinit-ℕ-isProp 𝒾 𝒿 u fe fe1 fe2 I@(cI , i₀ , iₛ) J@(cJ , j₀ , jₛ) fI gJ =
 pair⁼ (cI≡cJ , missing)
 where
  F : ℕHom 𝒾 𝒾 I J
  F = pr₁ (fI J)
  G : ℕHom 𝒾 𝒾 J I
  G = pr₁ (gJ I)
  f : cI → cJ
  f = pr₁ F
  g : cJ → cI
  g = pr₁ G

  g∘f≡id : g ∘ f ≡ id
  g∘f≡id = ap pr₁ (endoI-isProp (∘-ℕHom I J I F G) (id-ℕHom I))
   where
    endoI-isProp : isProp (ℕHom 𝒾 𝒾 I I)
    endoI-isProp = pr₂ (contr-are-pointed-props (ℕHom 𝒾 𝒾 I I) (fI I))

  f∘g≡id : f ∘ g ≡ id
  f∘g≡id = ap pr₁ (endoJ-isProp (∘-ℕHom J I J G F) (id-ℕHom J))
   where
    endoJ-isProp : isProp (ℕHom 𝒾 𝒾 J J)
    endoJ-isProp = pr₂ (contr-are-pointed-props (ℕHom 𝒾 𝒾 J J) (gJ J))

  cI≃cJ : cI ≃ cJ
  cI≃cJ = (f , invs-are-equivs f q-qinv-f)
   where
    q-qinv-f : qinv f
    q-qinv-f = (g , happly (f ∘ g) id f∘g≡id , happly (g ∘ f) id g∘f≡id)


  cI≡cJ : cI ≡ cJ
  cI≡cJ = ua u cI cJ cI≃cJ

  c : isProp ((C : ℕAlg 𝒾) → (D : ℕAlg 𝒾) → isContr (ℕHom 𝒾 𝒾 C D))
  c = Π-preserves-props fe2 (ℕAlg 𝒾)
   (λ C → (D : ℕAlg 𝒾) → isContr (ℕHom 𝒾 𝒾 C D)) b
   where
    b : (C : ℕAlg 𝒾) → isProp ((D : ℕAlg 𝒾) → isContr (ℕHom 𝒾 𝒾 C D))
    b C = Π-preserves-props fe1 (ℕAlg 𝒾)
      (λ D → isContr (ℕHom 𝒾 𝒾 C D))
      (λ D → isContr-isProp fe (ℕHom 𝒾 𝒾 C D))


  missing : tr (λ C → C × (C → C)) cI≡cJ (i₀ , iₛ) ≡
              (j₀ , jₛ)
  missing = begin
   tr (λ C → C × (C → C)) cI≡cJ (i₀ , iₛ) ≡⟨ tr× ⟩
   (tr (λ C → C) cI≡cJ i₀ ,
     tr (λ C → (C → C)) cI≡cJ iₛ)         ≡⟨ pair×⁼ (tr-i₀≡j₀ , tr-iₛ≡jₛ) ⟩
   (j₀ , jₛ) ∎
   where
    tr× : tr (λ C → C × (C → C)) cI≡cJ (i₀ , iₛ) ≡
          (tr (λ C → C) cI≡cJ i₀ , tr (λ C → (C → C)) cI≡cJ iₛ)
    tr× = trA×B (𝒰 𝒾) (λ C → C) (λ C → C → C) cI cJ cI≡cJ (i₀ , iₛ)

    tr-i₀≡j₀ : tr (λ C → C) (cI≡cJ) i₀ ≡ j₀
    tr-i₀≡j₀ = begin
      tr (λ C → C) (cI≡cJ) i₀ ≡⟨ ≡u-comp u cI≃cJ i₀ ⟩
      pr₁ cI≃cJ i₀            ≡⟨⟩
      f i₀                    ≡⟨ pr₁ (pr₂ F) ⟩
      j₀                      ∎

    tr-iₛ≡jₛ : tr (λ C → (C → C)) (cI≡cJ) iₛ ≡ jₛ
    tr-iₛ≡jₛ = _
     where
      x : tr (λ x → x → x) cI≡cJ iₛ ≡
            (λ x → tr id cI≡cJ (iₛ (tr id (cI≡cJ ⁻¹) x)))
      x = trf (𝒰 𝒾) id id cI cJ cI≡cJ iₛ
    -- st = begin
    --   tr (λ C → (C → C)) (cI≡cJ) i₀ ≡⟨ ≡u-comp u cI cJ cI≃cJ i₀ ⟩
    --   pr₁ cI≃cJ i₀                  ≡⟨⟩
    --   f i₀                          ≡⟨ pr₁ (pr₂ F) ⟩
    --   jₛ                            ∎

  related? : (cI × (cI → cI)) → (cJ × (cJ → cJ))
  related? = tr (λ C → C × (C → C)) cI≡cJ

  -- P : (A B : Σ C ꞉ (𝒰 𝒾) , C) → (pr₁ A ≡ pr₁ B) → A ≡ B
  -- P (A , a0) (B , b0) p = pair⁼(p , x)
  --  where
  --   x : tr (λ C → C) p a0 ≡ b0
  --   x = _
