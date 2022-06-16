{-# OPTIONS --without-K --exact-split --safe --auto-inline --no-import-sorts #-}

module Chapter3.Book where

open import Chapter2.Book public

-- Definition 3.1.1
is-set : 𝒰 𝒾 → 𝒰 𝒾
is-set X = (x y : X) (p q : x ≡ y) → (p ≡ q)

-- Example 3.1.2
𝟙-is-set : is-set 𝟙
𝟙-is-set x y p q =
  let (f , ((g , f-g) , (h , h-f))) = 𝟙-≡-≃ x y
      hfp≡hfq : h (f p) ≡ h (f q)
      hfp≡hfq = ap h (𝟙-is-subsingleton (f p) (f q))
  in  begin
    p ≡˘⟨ h-f p ⟩
    h (f p) ≡⟨ hfp≡hfq ⟩
    h (f q) ≡⟨ h-f q ⟩
    q ∎

-- Example 3.1.3
𝟘-is-set : is-set 𝟘
𝟘-is-set x y p q = !𝟘 (p ≡ q) x

-- 3.1.9
swap₂ : 𝟚 → 𝟚
swap₂ ₀ = ₁
swap₂ ₁ = ₀

swap₂-involutive : (n : 𝟚) → swap₂ (swap₂ n) ≡ n
swap₂-involutive ₀ = refl ₀
swap₂-involutive ₁ = refl ₁

swap₂-is-equiv : is-equiv swap₂
swap₂-is-equiv = invs-are-equivs
                  swap₂
                  (swap₂ , swap₂-involutive , swap₂-involutive)

e₀ e₁ : 𝟚 ≃ 𝟚
e₀ = ≃-refl 𝟚
e₁ = swap₂ , swap₂-is-equiv

swap₂-is-not-id : swap₂ ≢ 𝑖𝑑 𝟚
swap₂-is-not-id p = ₁-is-not-₀ (ap (λ f → f ₀) p)

e₀-is-not-e₁ : e₀ ≢ e₁
e₀-is-not-e₁ p = ₁-is-not-₀ r
 where
  q : id ≡ swap₂
  q = ap ⌜_⌝ p
  r : ₁ ≡ ₀
  r = ap (λ - → - ₁) q

-- Example 3.1.9
p-is-not-refl : (is-univalent lzero) → (¬ (is-set 𝒰₀))
p-is-not-refl ua is-set-𝒰₀ =
  let (Eq→Id' , (Id→Eq∘Eq→Id , Eq→IdId→Eq∘)) = qinv-ua ua 𝟚 𝟚
      p : 𝟚 ≡ 𝟚
      p = Eq→Id' e₁
      assumption : p ≡ refl 𝟚
      assumption = is-set-𝒰₀ 𝟚 𝟚 p (refl 𝟚)
      p≡refl : e₁ ≡ Id→Eq 𝟚 𝟚 (refl 𝟚)
      p≡refl = begin
        e₁                  ≡˘⟨ Id→Eq∘Eq→Id e₁ ⟩
        Id→Eq 𝟚 𝟚 p         ≡⟨ ap (Id→Eq 𝟚 𝟚) assumption ⟩
        Id→Eq 𝟚 𝟚 (refl 𝟚)  ∎
      swap₂≡id : swap₂ ≡ 𝑖𝑑 𝟚
      swap₂≡id = ap pr₁ p≡refl
   in swap₂-is-not-id swap₂≡id

---------------------------------------------------------------------------------

-- Theorem 3.2.2

-- Corollary 3.27

---------------------------------------------------------------------------------

-- 3.3 Mere Propositions

-- Definition 3.3.1
isProp : (P : 𝒰 𝒾) → 𝒰 𝒾
isProp P = (x y : P) → x ≡ y

-- Lemma 3.3.2

-- Lemma 3.3.3
isProp-LogEq→Eq : (P Q : 𝒰 𝒾) → isProp P → isProp Q
                  → (P → Q) → (Q → P) → (P ≃ Q)
isProp-LogEq→Eq P Q pP pQ f g = f , (invs-are-equivs f (g , f∘g∼id , g∘f∼id))
  where
    f∘g∼id : f ∘ g ∼ id
    f∘g∼id y = pQ (f (g y)) y
    g∘f∼id : g ∘ f ∼ id
    g∘f∼id x = pP (g (f x)) x

---------------------------------------------------------------------------------

-- 3.4 Classical vs. intuitionistic logic

-- Definition 3.4.3
decidable : 𝒰 𝒾 → 𝒰 𝒾
decidable A = A ⊎ ¬ A

decidable-family : (A : 𝒰 𝒾) (B : A → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
decidable-family A B = (a : A) → (B a) ⊎ (¬ (B a))

has-decidable-equality : 𝒰 𝒾 → 𝒰 𝒾
has-decidable-equality X = (x y : X) → decidable (x ≡ y)

---------------------------------------------------------------------------------

-- 3.5 Subsets and propositional resizing

Prop𝒰 : (𝒾 : Level) → 𝒰 (𝒾 ⁺)
Prop𝒰 𝒾 = Σ A ꞉ (𝒰 𝒾) , isProp(A)

-- Helper to have cumulativity
record Lift (A : 𝒰 𝒾) : 𝒰 (𝒾 ⁺) where
  constructor lift'
  field unlift : A

Prop𝒰→𝒰⁺ : {𝒾 : Level} → (Prop𝒰 𝒾) → (Prop𝒰 (𝒾 ⁺))
Prop𝒰→𝒰⁺ (X , f) = Lift X , isProp-Lift X f
  where
    isProp-Lift : (A : 𝒰 𝒾) → isProp A → isProp (Lift A)
    isProp-Lift A p x y = ap lift' (p (Lift.unlift x) (Lift.unlift y))

-- Similar to the is-univalent definition
is-propres : (𝒾 : Level) → 𝒰 (𝒾 ⁺ ⁺)
is-propres 𝒾 = is-equiv (Prop𝒰→𝒰⁺ {𝒾})

-- Axiom 3.5.5
PropositionalResizing : 𝓤ω
PropositionalResizing = ∀ 𝒾 → is-propres 𝒾

---------------------------------------------------------------------------------

-- 3.6 The logic of mere propositions
record subsingleton-truncations-exist : 𝓤ω where
  field
    ∥_∥                  : {𝒾 : Level} → 𝒰 𝒾 → 𝒰 𝒾
    ∥∥-is-subsingleton   : {𝒾 : Level} {X : 𝒰 𝒾} → isProp (∥ X ∥)
    ∣_∣                  : {𝒾 : Level} {X : 𝒰 𝒾} → X → ∥ X ∥
    ∥∥-recursion         : {𝒾 𝒿 : Level} {X : 𝒰 𝒾} {P : 𝒰 𝒿}
                           → isProp P → (X → P) → ∥ X ∥ → P
  infix 0 ∥_∥

---------------------------------------------------------------------------------

-- 3.11 Contractibility

-- Definition 3.11.1
isContr : 𝒰 𝒾 → 𝒰 𝒾
isContr A = Σ a ꞉ A , ((x : A) → a ≡ x)

-- Lemma 3.11.3


-- Lemma 3.11.4
isContr-isProp : (A : 𝒰 𝒾) → isProp(isContr A)
isContr-isProp A (a , p) (a' , p') = pair⁼ (q , q')
  where
    q : a ≡ a'
    q = p a'
    q' : tr (λ - → (x : A) → - ≡ x) q p ≡ p'
    q' = {!!}
