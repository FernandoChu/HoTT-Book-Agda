{-# OPTIONS --without-K --exact-split --safe --auto-inline --no-import-sorts #-}

module Chapter3.Book where

open import Chapter2.Book public

---------------------------------------------------------------------------------

-- 3.1 Sets and n-types

-- Definition 3.1.1
isSet : 𝒰 𝒾 → 𝒰 𝒾
isSet X = (x y : X) (p q : x ≡ y) → (p ≡ q)

-- Example 3.1.2
𝟙-isSet : isSet 𝟙
𝟙-isSet x y p q =
  let (f , ((g , f-g) , (h , h-f))) = 𝟙-≡-≃ x y
      hfp≡hfq : h (f p) ≡ h (f q)
      hfp≡hfq = ap h (𝟙-is-subsingleton (f p) (f q))
  in  begin
    p       ≡˘⟨ h-f p ⟩
    h (f p) ≡⟨ hfp≡hfq ⟩
    h (f q) ≡⟨ h-f q ⟩
    q       ∎

-- Example 3.1.3
𝟘-isSet : isSet 𝟘
𝟘-isSet x y p q = !𝟘 (p ≡ q) x

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
p-is-not-refl : (is-univalent lzero) → (¬ (isSet 𝒰₀))
p-is-not-refl u is-set-𝒰₀ = swap₂-is-not-id swap₂≡id
  where
    p : 𝟚 ≡ 𝟚
    p = ua u e₁
    assumption : p ≡ refl 𝟚
    assumption = is-set-𝒰₀ 𝟚 𝟚 p (refl 𝟚)
    p≡refl : e₁ ≡ idtoeqv (refl 𝟚)
    p≡refl = begin
      e₁                ≡⟨ id∼idtoeqv∘ua u e₁ ⟩
      idtoeqv (ua u e₁) ≡⟨ ap (idtoeqv) assumption ⟩
      idtoeqv (refl 𝟚)  ∎
    swap₂≡id : swap₂ ≡ 𝑖𝑑 𝟚
    swap₂≡id = ap pr₁ p≡refl

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

-- Lemma 3.3.4
props-are-sets : (A : 𝒰 𝒾) → isProp A → isSet A
props-are-sets A f x y p q = (claim2 x y p) ∙ (claim2 x y q)⁻¹
  where
    g : (z : A) → x ≡ z
    g z = f x z
    claim1 : (y z : A) (p : y ≡ z) → g y ∙ p ≡ g z
    claim1 y z p = begin
      g(y) ∙ p                  ≡˘⟨ trHomc- x y z p (f x y) ⟩
      tr (λ - → x ≡ -) p (g(y)) ≡⟨ apd g p ⟩
      g z                       ∎
    claim2 : (y z : A) (p : y ≡ z) → p ≡ (g y)⁻¹ ∙ g z
    claim2 y z p = begin
      p ≡˘⟨ refl-left ⟩
      (refl y) ∙ p        ≡˘⟨ ap (λ - → - ∙ p) (⁻¹-left∙ (g y)) ⟩
      ((g y)⁻¹ ∙ g y) ∙ p ≡⟨ ∙-assoc ((g y)⁻¹) ⟩
      (g y)⁻¹ ∙ (g y ∙ p) ≡⟨ ap (λ - → (g y)⁻¹ ∙ -) (claim1 y z p) ⟩
      (g y)⁻¹ ∙ g z       ∎


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

-- Example 3.6.2
Π-preserves-props : {𝒾 𝒿 : Level} → has-funext 𝒾 𝒿 →
                    (A : 𝒰 𝒾) (B : A → 𝒰 𝒿) →
                    ((x : A) → isProp (B x)) → isProp ((x : A) → B x)
Π-preserves-props fe A B p f g = pr₁ (pr₁ (fe f g)) (λ x → p x (f x) (g x))

---------------------------------------------------------------------------------

-- 3.7 Propositional truncation

-- Workaround: non cubical agda must express truncations in this manner
-- and the existence of an element of this type must be postulated or assumed
-- for a particular statement.

record subsingleton-truncations-exist : 𝓤ω where
  field
    ∥_∥                  : {𝒾 : Level} → 𝒰 𝒾 → 𝒰 𝒾
    ∥∥-is-subsingleton   : {𝒾 : Level} {X : 𝒰 𝒾} → isProp (∥ X ∥)
    ∣_∣                  : {𝒾 : Level} {X : 𝒰 𝒾} → X → ∥ X ∥
    ∥∥-recursion         : {𝒾 𝒿 : Level} {X : 𝒰 𝒾} {P : 𝒰 𝒿}
                           → isProp P → (X → P) → ∥ X ∥ → P
  infix 0 ∥_∥

module subsingleton-truncations
       (pt  : subsingleton-truncations-exist)
       where
  open subsingleton-truncations-exist pt public


---------------------------------------------------------------------------------

-- 3.8 The axiom of choice

---------------------------------------------------------------------------------

-- 3.9 The principle of unique choice

  truncations-fixes-props : (P : 𝒰 𝒾) → isProp P → (P ≃ ∥ P ∥)
  truncations-fixes-props P p =
    isProp-LogEq→Eq P (∥ P ∥) p ∥∥-is-subsingleton ∣_∣ (∥∥-recursion p id)

---------------------------------------------------------------------------------

-- 3.11 Contractibility

-- Definition 3.11.1
isContr : 𝒰 𝒾 → 𝒰 𝒾
isContr A = Σ a ꞉ A , ((x : A) → a ≡ x)

-- Lemma 3.11.3
contr-are-pointed-props : (A : 𝒰 𝒾) → isContr A → A × isProp A
contr-are-pointed-props A (a , p) = (a , λ x y → (p x)⁻¹ ∙ (p y))

pointed-props-are-contr : (A : 𝒰 𝒾) → A × isProp A → isContr A
pointed-props-are-contr A (a , p) = (a , λ x → p a x)

-- Lemma 3.11.4
isContr-isProp : {𝒾 : Level} → has-funext 𝒾 𝒾 → (A : 𝒰 𝒾) → isProp(isContr A)
isContr-isProp fe A (a , p) (a' , p') = pair⁼ (q , q')
  where
    q : a ≡ a'
    q = p a'
    a≡x-isProp : (x : A) → isProp (a' ≡ x)
    a≡x-isProp x r s =
      props-are-sets A (pr₂ (contr-are-pointed-props A (a , p))) a' x r s
    q' : tr (λ - → (x : A) → - ≡ x) q p ≡ p'
    q' = Π-preserves-props fe A (λ x → a' ≡ x) a≡x-isProp
           (tr (λ - → (x : A) → - ≡ x) q p) p'

-- Corollary 3.11.5
isContr-isContr : has-funext 𝒾 𝒾 → (A : 𝒰 𝒾) → isContr A → isContr (isContr A)
isContr-isContr fe A c =
  pointed-props-are-contr (isContr A) (c , (isContr-isProp fe A))

-- Lemma 3.11.6
Π-preserves-contr : {𝒾 𝒿 : Level} → has-funext 𝒾 𝒿 →
                    (A : 𝒰 𝒾) (B : A → 𝒰 𝒿) →
                    ((x : A) → isContr (B x)) → isContr ((x : A) → B x)
Π-preserves-contr fe A B p =
  pointed-props-are-contr ((x : A) → B x) (f , Π-isProp)
  where
    f : (x : A) → B x
    f x = pr₁ (p x)
    Bx-isProp : (x : A) → isProp (B x)
    Bx-isProp x = pr₂ (contr-are-pointed-props (B x) (p x))
    Π-isProp : isProp ((x : A) → B x)
    Π-isProp = Π-preserves-props fe A B Bx-isProp

has-section : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 (𝒾 ⊔ 𝒿)
has-section r = Σ s ꞉ (codomain r → domain r), r ∘ s ∼ id

-- We say that X is a retract of Y, written X ◁ Y,
-- if we have a function Y → X which has a section:
_◁_ : 𝒰 𝒾 → 𝒰 𝒿 → 𝒰 (𝒾 ⊔ 𝒿)
X ◁ Y = Σ r ꞉ (Y → X), has-section r

-- Helpers
retraction : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ◁ Y → Y → X
retraction (r , s , ε) = r

section : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ◁ Y → X → Y
section (r , s , ε) = s


retract-equation : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (ρ : X ◁ Y)
                 → retraction ρ ∘ section ρ ∼ 𝑖𝑑 X
retract-equation (r , s , ε) = ε

retraction-has-section : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (ρ : X ◁ Y)
                       → has-section (retraction ρ)
retraction-has-section (r , h) = h

-- Lemma 3.11.7
rectraction-of-contr-isContr :
  (B : 𝒰 𝒾) (A : 𝒰 𝒿) → B ◁ A → isContr A → isContr B
rectraction-of-contr-isContr B A (r , s , ε) (a₀ , contr) =
  (b₀ , λ b → (p b)⁻¹)
    where
      b₀ : B
      b₀ = r a₀
      p : (b : B) → b ≡ b₀
      p b = (ε b)⁻¹ ∙ ap r (contr (s b)⁻¹)

-- Lemma 3.11.8
based-paths-isContr : (A : 𝒰 𝒾) (a : A) → isContr (Σ x ꞉ A , a ≡ x)
based-paths-isContr A a = ( (a , refl a) , f )
  where
    f : (xp : Σ x ꞉ A , a ≡ x) → (a , refl a) ≡ xp
    f (x , p) = pair⁼(p , ((trHomc- a a x p (refl a)) ∙ refl-left))

-- Lemma 3.11.9

-- Lemma 3.11.10
props-if-contr-Id : (A : 𝒰 𝒾)
                    → ((x y : A) → isContr (x ≡ y))
                    → isProp A
props-if-contr-Id A f x y = pr₁ (f x y)

props-have-contr-Id : (A : 𝒰 𝒾) → isProp A
                    → ((x y : A) → isContr (x ≡ y))
props-have-contr-Id A f x y =
  pointed-props-are-contr (x ≡ y) (f x y , P)
    where
      P : isProp (x ≡ y)
      P p q = props-are-sets A f x y p q
