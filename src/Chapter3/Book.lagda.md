---isNType-Σ
title: Chapter 3. Sets and logic
---

# Chapter 3. Sets and logic

```agda
module Chapter3.Book where

open import Chapter2.Exercises public
```

## 3.1 Sets and n-types

```agda
-- Definition 3.1.1.
isSet : 𝒰 𝒾 → 𝒰 𝒾
isSet X = {x y : X} (p q : x ≡ y) → (p ≡ q)

-- Example 3.1.2.
isSet-𝟙 : isSet 𝟙
isSet-𝟙 {x} {y} p q =
  let (f , ((g , f-g) , (h , h-f))) = ≡-𝟙-≃ x y
      hfp≡hfq : h (f p) ≡ h (f q)
      hfp≡hfq = ap h (isProp-𝟙 (f p) (f q))
  in  begin
    p       ≡˘⟨ h-f p ⟩
    h (f p) ≡⟨ hfp≡hfq ⟩
    h (f q) ≡⟨ h-f q ⟩
    q       ∎

-- Example 3.1.3.
isSet-𝟘 : isSet 𝟘
isSet-𝟘 {x} {y} p q = !𝟘 (p ≡ q) x

isProp-𝟘 : (x y : 𝟘) → x ≡ y
isProp-𝟘 x y = !𝟘 (x ≡ y) x

-- Example 3.1.4.
isSet-ℕ : isSet ℕ
isSet-ℕ {m} {n} p q =
  p                             ≡˘⟨ ≃-η (≡-ℕ-≃ m n) p ⟩
  decode-ℕ m n (encode-ℕ m n p) ≡⟨ ap (decode-ℕ m n) (lemma m n _ _) ⟩
  decode-ℕ m n (encode-ℕ m n q) ≡⟨ ≃-η (≡-ℕ-≃ m n) q ⟩
  q ∎
 where
  lemma : (m n : ℕ) (p q : code-ℕ m n) → p ≡ q
  lemma zero zero p q         = isProp-𝟙 p q
  lemma (succ m) zero p q     = isProp-𝟘 p q
  lemma zero (succ n) p q     = isProp-𝟘 p q
  lemma (succ m) (succ n) p q = lemma m n p q

-- Example 3.1.5.
isSet-× : {A : 𝒰 𝒾}
        → {B : 𝒰 𝒿}
        → isSet A
        → isSet B
        → isSet (A × B)
isSet-× f g p q = begin
  p                           ≡⟨ ≡-×-uniq p ⟩
  pair×⁼(ap pr₁ p , ap pr₂ p) ≡⟨ ap (λ - → pair×⁼(- , ap pr₂ p)) (f _ _) ⟩
  pair×⁼(ap pr₁ q , ap pr₂ p) ≡⟨ ap (λ - → pair×⁼(ap pr₁ q , -)) (g _ _) ⟩
  pair×⁼(ap pr₁ q , ap pr₂ q) ≡˘⟨ ≡-×-uniq q ⟩
  q                           ∎

-- Example 3.1.6.
isSet-Π : {A : 𝒰 𝒾}
        → {B : A → 𝒰 𝒿}
        → ((x : A) → isSet (B x))
        → isSet (Π B)
isSet-Π isSet-Bx {f} {g} p q = begin
  p                 ≡⟨ ≡-Π-uniq p ⟩
  funext (happly p) ≡⟨ ap funext (funext (λ - → isSet-Bx - _ _)) ⟩
  funext (happly q) ≡˘⟨ ≡-Π-uniq q ⟩
  q ∎

-- Definition 3.1.7.
is1Type : (A : 𝒰 𝒾) → 𝒰 𝒾
is1Type A = {x y : A} {p q : x ≡ y}
            → (r s : p ≡ q)
            → r ≡ s

-- Lemma 3.1.8.
isSet⇒is1Type : {A : 𝒰 𝒾}
              → isSet A
              → is1Type A
isSet⇒is1Type f {x} {y} {p} {q} r s = begin
  r ≡˘⟨ refl-left ⟩
  refl _ ∙ r          ≡˘⟨ ap (_∙ r) (⁻¹-left∙ (g p)) ⟩
  (g p)⁻¹ ∙ g p ∙ r   ≡⟨ ∙-assoc (g p ⁻¹) ⟩
  (g p)⁻¹ ∙ (g p ∙ r) ≡⟨ ap (_ ∙_) (lemma p q r) ⟩
  (g p)⁻¹ ∙ g q       ≡˘⟨ ap (_ ∙_) (lemma p q s) ⟩
  (g p)⁻¹ ∙ (g p ∙ s) ≡˘⟨ ∙-assoc (g p ⁻¹) ⟩
  (g p)⁻¹ ∙ g p ∙ s   ≡⟨ ap (_∙ s) (⁻¹-left∙ (g p)) ⟩
  refl _ ∙ s          ≡⟨ refl-left ⟩
  s ∎
 where
  g : (q : x ≡ y) → p ≡ q
  g q = f p q
  lemma : (q q' : x ≡ y) (r : q ≡ q') → g q ∙ r ≡ g q'
  lemma q q' r = (tr-Homc─ p r _)⁻¹ ∙ apd g r

-- Example 3.1.9.
swap₂ : 𝟚 → 𝟚
swap₂ ₀ = ₁
swap₂ ₁ = ₀

involutive-swap₂ : (n : 𝟚) → swap₂ (swap₂ n) ≡ n
involutive-swap₂ ₀ = refl ₀
involutive-swap₂ ₁ = refl ₁

isEquiv-swap₂ : isEquiv swap₂
isEquiv-swap₂ = invs⇒equivs
                  swap₂
                  (swap₂ , involutive-swap₂ , involutive-swap₂)

e₀ e₁ : 𝟚 ≃ 𝟚
e₀ = ≃-refl 𝟚
e₁ = swap₂ , isEquiv-swap₂

swap₂≢id : swap₂ ≢ 𝑖𝑑 𝟚
swap₂≢id p = ₁-is-not-₀ (ap (λ f → f ₀) p)

e₀≢e₁ : e₀ ≢ e₁
e₀≢e₁ p = ₁-is-not-₀ r
 where
  q : id ≡ swap₂
  q = ap ≃-→ p
  r : ₁ ≡ ₀
  r = ap (λ - → - ₁) q

¬-isSet-𝒰₀ : ¬ (isSet 𝒰₀)
¬-isSet-𝒰₀ isSet-𝒰₀ = swap₂≢id swap₂≡id
  where
    p : 𝟚 ≡ 𝟚
    p = ua e₁
    assumption : p ≡ refl 𝟚
    assumption = isSet-𝒰₀ {𝟚} {𝟚} p (refl 𝟚)
    p≡refl : e₁ ≡ idtoeqv (refl 𝟚)
    p≡refl = begin
      e₁                ≡⟨ (≃-ε (≡-≡-≃ 𝟚 𝟚) e₁)⁻¹  ⟩
      idtoeqv (ua e₁)   ≡⟨ ap (idtoeqv) assumption ⟩
      idtoeqv (refl 𝟚)  ∎
    swap₂≡id : swap₂ ≡ 𝑖𝑑 𝟚
    swap₂≡id = ap pr₁ p≡refl
```

## 3.2 Propositions as types?

```agda
-- Theorem 3.2.2.
hasRAA : 𝒰 𝒾 → 𝒰 𝒾
hasRAA A = ¬¬ A → A

-- Corollary 3.27.
```

## 3.3 Mere Propositions

```agda
-- Definition 3.3.1.
isProp : (P : 𝒰 𝒾) → 𝒰 𝒾
isProp P = (x y : P) → x ≡ y

-- Lemma 3.3.2.
isPointedProp≃𝟙 : (P : 𝒰 𝒾) → (x₀ : P) → (isProp P) → P ≃ 𝟙
isPointedProp≃𝟙 P x₀ f = (λ - → ⋆) ,
  invs⇒equivs (λ - → ⋆) ((λ - → x₀) , (λ x → isProp-𝟙 ⋆ x) , (λ x → f x₀ x))

-- Lemma 3.3.3.
isProp-areLogEq⇒Eq : (P Q : 𝒰 𝒾) → isProp P → isProp Q
                  → (P → Q) → (Q → P) → (P ≃ Q)
isProp-areLogEq⇒Eq P Q pP pQ f g = f , (invs⇒equivs f (g , f∘g∼id , g∘f∼id))
  where
    f∘g∼id : f ∘ g ∼ id
    f∘g∼id y = pQ (f (g y)) y
    g∘f∼id : g ∘ f ∼ id
    g∘f∼id x = pP (g (f x)) x

-- Lemma 3.3.4.
isProp⇒isSet : {A : 𝒰 𝒾} → isProp A → isSet A
isProp⇒isSet {𝒾} {A} f {x} {y} p q = (claim2 x y p) ∙ (claim2 x y q)⁻¹
  where
    g : (z : A) → x ≡ z
    g z = f x z
    claim1 : (y z : A) (p : y ≡ z) → g y ∙ p ≡ g z
    claim1 y z p = begin
      g(y) ∙ p                  ≡˘⟨ tr-Homc─ x p (f x y) ⟩
      tr (λ - → x ≡ -) p (g(y)) ≡⟨ apd g p ⟩
      g z                       ∎
    claim2 : (y z : A) (p : y ≡ z) → p ≡ (g y)⁻¹ ∙ g z
    claim2 y z p = begin
      p ≡˘⟨ refl-left ⟩
      (refl y) ∙ p        ≡˘⟨ ap (λ - → - ∙ p) (⁻¹-left∙ (g y)) ⟩
      ((g y)⁻¹ ∙ g y) ∙ p ≡⟨ ∙-assoc ((g y)⁻¹) ⟩
      (g y)⁻¹ ∙ (g y ∙ p) ≡⟨ ap (λ - → (g y)⁻¹ ∙ -) (claim1 y z p) ⟩
      (g y)⁻¹ ∙ g z       ∎

-- Lemma 3.3.5.
isProp-isProp : (A : 𝒰 𝒾) → isProp (isProp A)
isProp-isProp A f g =
  funext λ x → funext (λ y → isProp⇒isSet f _ _)
```

## 3.4 Classical vs. intuitionistic logic

```agda
-- Definition 3.4.3.
isDecidable : 𝒰 𝒾 → 𝒰 𝒾
isDecidable A = A ⊎ ¬ A

isDecidableFamily : {A : 𝒰 𝒾} (B : A → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
isDecidableFamily {A = A} B = (a : A) → isDecidable (B a)

hasDecidableEquality : 𝒰 𝒾 → 𝒰 𝒾
hasDecidableEquality X = (x y : X) → isDecidable (x ≡ y)
```

## 3.5 Subsets and propositional resizing

```agda
-- Lemma 3.5.1.
isProp-≡-₁⇒≡ : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿}
            → ((x : A) → isProp (P x))
            → (u v : Σ P) → pr₁ u ≡ pr₁ v
            → u ≡ v
isProp-≡-₁⇒≡ f u v p = pair⁼(p , f _ _ _)

Set𝒰 : (𝒾 : Level) → 𝒰 (𝒾 ⁺)
Set𝒰 𝒾 = Σ A ꞉ (𝒰 𝒾) , isSet(A)

Prop𝒰 : (𝒾 : Level) → 𝒰 (𝒾 ⁺)
Prop𝒰 𝒾 = Σ A ꞉ (𝒰 𝒾) , isProp(A)

Prop𝒰→𝒰⁺ : (𝒾 : Level) → (Prop𝒰 𝒾) → (Prop𝒰 (𝒾 ⁺))
Prop𝒰→𝒰⁺ 𝒾 (X , f) = Raised (𝒾 ⁺) X , isProp-Lift X f
  where
    isProp-Lift : (A : 𝒰 𝒾) → isProp A → isProp (Raised (𝒾 ⁺) A)
    isProp-Lift A p x y = begin
      x ≡˘⟨ ≃-η (≡-Raised-≃ (𝒾 ⁺) A) x ⟩
      raise (raise⁻¹ (𝒾 ⁺) A x) ≡⟨ ap raise (p (raise⁻¹ (𝒾 ⁺) A x)
                                      (raise⁻¹ (𝒾 ⁺) A y)) ⟩
      raise (raise⁻¹ (𝒾 ⁺) A y) ≡⟨ ≃-η (≡-Raised-≃ (𝒾 ⁺) A) y ⟩
      y ∎

-- Axiom 3.5.5.
PropRes : (𝒾 : Level) → 𝒰 (𝒾 ⁺⁺)
PropRes 𝒾 = isEquiv (Prop𝒰→𝒰⁺ (𝒾))
```

## 3.6 The logic of mere propositions

```agda
-- Example 3.6.2.
isProp-Π : {𝒾 𝒿 : Level}
           {A : 𝒰 𝒾} {B : A → 𝒰 𝒿}
         → ((x : A) → isProp (B x)) → isProp ((x : A) → B x)
isProp-Π p f g = funext (λ x → p x (f x) (g x))
```

## 3.7 Propositional truncation

```agda
postulate
  ∥_∥ : {𝒾 : Level} → (A : 𝒰 𝒾) → 𝒰 𝒾
  ∣_∣ : {𝒾 : Level} → {A : 𝒰 𝒾} → A → ∥ A ∥
  ∥∥-isProp : {X : 𝒰 𝒾} → isProp (∥ X ∥)
  ∥∥-rec : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
          → isProp B
          → (g : A → B)
          → ∥ A ∥ → B
  ∥∥-rec-comp : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
               → (p : isProp B)
               → (g : A → B)
               → (a : A)
               → ∥∥-rec A B p g (∣ a ∣) ≡ g a
  {-# REWRITE ∥∥-rec-comp #-}
```

## 3.8 The axiom of choice

```agda
--
```

## 3.9 The principle of unique choice

```agda
isProp⇒─≃∥─∥ : (P : 𝒰 𝒾) → isProp P → (P ≃ ∥ P ∥)
isProp⇒─≃∥─∥ P p =
  isProp-areLogEq⇒Eq P (∥ P ∥) p ∥∥-isProp ∣_∣ (∥∥-rec P P p id)
```

## 3.11 Contractibility

```agda
-- Definition 3.11.1.
isContr : 𝒰 𝒾 → 𝒰 𝒾
isContr A = Σ a ꞉ A , ((x : A) → a ≡ x)

-- Lemma 3.11.3.
isContr⇒isProp : (A : 𝒰 𝒾) → isContr A → isProp A
isContr⇒isProp A (a , p) x y = (p x)⁻¹ ∙ (p y)

isContr⇒isPointedProp : (A : 𝒰 𝒾) → isContr A → A × isProp A
isContr⇒isPointedProp A (a , p) = (a , isContr⇒isProp A (a , p))

isPointedProp⇒isContr : (A : 𝒰 𝒾) → A × (isProp A) → isContr A
isPointedProp⇒isContr A (a , p) = (a , λ x → p a x)

isPointedProp-𝟙 : 𝟙 × (isProp 𝟙)
isPointedProp-𝟙 = (⋆ , isProp-𝟙)

≃𝟙⇒isPointedProp : (A : 𝒰 𝒾) → A ≃ 𝟙 → (A × isProp A)
≃𝟙⇒isPointedProp A (f , eqv) =
  let ( g , f∘g , g∘f ) = equivs⇒invs f eqv
   in ( g ⋆ , λ x y → (g∘f x)⁻¹ ∙ ap g (isProp-𝟙 (f x) (f y)) ∙ g∘f y)

-- Helpers
isContr⇒≃𝟙 : (A : 𝒰 𝒾) → isContr A → A ≃ 𝟙
isContr⇒≃𝟙 A ap =
  let ( a , p ) = isContr⇒isPointedProp A ap
   in isPointedProp≃𝟙 A a p

≃𝟙⇒isContr : (A : 𝒰 𝒾) → A ≃ 𝟙 → isContr A
≃𝟙⇒isContr A feqv =
  let ( a , p ) = ≃𝟙⇒isPointedProp A feqv
   in isPointedProp⇒isContr A (a , p)

-- Lemma 3.11.4.
isProp-isContr : {𝒾 : Level} → (A : 𝒰 𝒾) → isProp(isContr A)
isProp-isContr A (a , p) (a' , p') = pair⁼ (q , q')
  where
    q : a ≡ a'
    q = p a'
    a≡x-isProp : (x : A) → isProp (a' ≡ x)
    a≡x-isProp x r s =
      isProp⇒isSet (pr₂ (isContr⇒isPointedProp A (a , p))) r s
    q' : tr (λ - → (x : A) → - ≡ x) q p ≡ p'
    q' = isProp-Π a≡x-isProp
           (tr (λ - → (x : A) → - ≡ x) q p) p'

-- Corollary 3.11.5.
isContr⇒isContr-isContr : (A : 𝒰 𝒾) → isContr A → isContr (isContr A)
isContr⇒isContr-isContr A c =
  isPointedProp⇒isContr (isContr A) (c , isProp-isContr A)

-- Lemma 3.11.6.
isContr-Π : {𝒾 𝒿 : Level} →
            {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} →
            ((x : A) → isContr (B x)) → isContr ((x : A) → B x)
isContr-Π {A = A} {B = B} p =
  isPointedProp⇒isContr ((x : A) → B x) (f , Π-isProp)
  where
    f : (x : A) → B x
    f x = pr₁ (p x)
    isProp-Bx : (x : A) → isProp (B x)
    isProp-Bx x = pr₂ (isContr⇒isPointedProp (B x) (p x))
    Π-isProp : isProp ((x : A) → B x)
    Π-isProp = isProp-Π isProp-Bx

hasSection : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 (𝒾 ⊔ 𝒿)
hasSection r = Σ s ꞉ (codomain r → domain r), r ∘ s ∼ id

-- We say that X is a retract of Y, written X ◁ Y,
-- if we have a function Y → X which has a section:
_◁_ : 𝒰 𝒾 → 𝒰 𝒿 → 𝒰 (𝒾 ⊔ 𝒿)
X ◁ Y = Σ r ꞉ (Y → X), hasSection r

-- Helpers
retraction : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ◁ Y → Y → X
retraction (r , s , ε) = r

section : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ◁ Y → X → Y
section (r , s , ε) = s

retract-equation : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (ρ : X ◁ Y)
                 → retraction ρ ∘ section ρ ∼ 𝑖𝑑 X
retract-equation (r , s , ε) = ε

-- Lemma 3.11.7.
retraction-isContr⇒isContr :
  {B : 𝒰 𝒾} {A : 𝒰 𝒿} → B ◁ A → isContr A → isContr B
retraction-isContr⇒isContr {B = B} (r , s , ε) (a₀ , contr) =
  (b₀ , λ b → (p b)⁻¹)
    where
      b₀ : B
      b₀ = r a₀
      p : (b : B) → b ≡ b₀
      p b = (ε b)⁻¹ ∙ ap r (contr (s b)⁻¹)

-- Lemma 3.11.8.
isContr-BasedPaths : {A : 𝒰 𝒾} (a : A) → isContr (Σ x ꞉ A , a ≡ x)
isContr-BasedPaths {𝒾} {A} a = ( (a , refl a) , f )
  where
    f : (xp : Σ x ꞉ A , a ≡ x) → (a , refl a) ≡ xp
    f (x , p) = pair⁼(p , ((tr-Homc─ a p (refl a)) ∙ refl-left))

-- Lemma 3.11.9.
isContr-Σ⇒base : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿)
               → ((x : A) → isContr (P x))
               → (Σ x ꞉ A , P x) ≃ A
isContr-Σ⇒base P f = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = pr₁
  map⁻¹ = λ a → (a , pr₁ (f a))
  ε = λ a → refl a
  η = λ (a , pa) → pair⁼ (refl a , pr₂ (f a) pa)

-- Lemma 3.11.10.
isContr-≡⇒isProp : {A : 𝒰 𝒾}
                 → ((x y : A) → isContr (x ≡ y))
                 → isProp A
isContr-≡⇒isProp f x y = pr₁ (f x y)

isProp⇒isContr-≡ : {A : 𝒰 𝒾} → isProp A
                 → ((x y : A) → isContr (x ≡ y))
isProp⇒isContr-≡ f x y =
  isPointedProp⇒isContr (x ≡ y) (f x y , P)
    where
      P : isProp (x ≡ y)
      P p q = isProp⇒isSet f p q
```
