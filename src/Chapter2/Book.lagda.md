---
title: Chapter 2. Homotopy Type Theory
---

# Chapter 2. Homotopy Type Theory

```agda
module Chapter2.Book where

open import Chapter1.Exercises public
```

## Section 2.1 Types are higher groupoids

```agda
-- Lemma 2.1.1.
_⁻¹ : {A : 𝒰 𝒾} → {x y : A} → x ≡ y → y ≡ x
(refl x)⁻¹ = refl x
infix  40 _⁻¹

-- Lemma 2.1.2.
_∙_ : {A : 𝒰 𝒾} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(refl x) ∙ (refl x) = (refl x)
infixl 30 _∙_
```

Similarly to the book, we can introduce equational reasoning in agda.
I'm using the definitions from the [agda-stdlib](https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#2708).

```agda
begin_ : {A : 𝒰 𝒾} {x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y
infix  1 begin_

_≡⟨⟩_ : {A : 𝒰 𝒾} (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

step-≡ : {A : 𝒰 𝒾} (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = x≡y ∙ y≡z
syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

step-≡˘ : {A : 𝒰 𝒾} (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
step-≡˘ _ y≡z y≡x = (y≡x)⁻¹ ∙ y≡z
syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
infixr 2 _≡⟨⟩_ step-≡ step-≡˘

_∎ : {A : 𝒰 𝒾} (x : A) → x ≡ x
_∎ x = refl x
infix  3 _∎
```

```agda
-- Lemma 2.1.4 i)
refl-left : {A : 𝒰 𝒾} {x y : A} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {A} {x} {x} {refl x} = refl (refl x)

refl-right : {A : 𝒰 𝒾} {x y : A} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {A} {x} {y} {refl x} = refl (refl x)

-- Lemma 2.1.4 ii)
⁻¹-left∙ : {A : 𝒰 𝒾} {x y : A} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {A : 𝒰 𝒾} {x y : A} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)

-- Lemma 2.1.4 iii)
⁻¹-involutive : {A : 𝒰 𝒾} {x y : A} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)

-- Lemma 2.1.4 iv)
∙-assoc : {A : 𝒰 𝒾} {x y z t : A} (p : x ≡ y) {q : y ≡ z} {r : z ≡ t}
        → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc (refl x) {refl x} {refl x} = refl (refl x)

-- Additional helper
⁻¹-∙ : {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y) {q : y ≡ z}
     → (p ∙ q)⁻¹ ≡  (q)⁻¹ ∙ (p)⁻¹
⁻¹-∙ (refl x) {refl x} = refl (refl x)

-- Definition 2.1.7.
𝒰∙ : (𝒾 : Level) → 𝒰 (𝒾 ⁺)
𝒰∙ 𝒾 = Σ A ꞉ (𝒰 𝒾) , A

-- Definition 2.1.8
Ω : ((A , a) : (𝒰∙ 𝒾)) → 𝒰∙ 𝒾
Ω (A , a) = ((a ≡ a) , refl a)

Ωⁿ : (n : ℕ) → ((A , a) : (𝒰∙ 𝒾)) → 𝒰∙ 𝒾
Ωⁿ 0 (A , a) = (A , a)
Ωⁿ (succ n) (A , a) = Ωⁿ n (Ω (A , a))
```

## Section 2.2 Functions are functors

```agda
ap : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) {x x' : A} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} (refl x) = refl (f x)

-- Lemma 2.2.2 i)
ap-∙ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) {x y z : A}
       (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f (refl x) (refl x) = refl (refl (f x))

-- Lemma 2.2.2 ii)
ap-⁻¹ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B) {x y : A} (p : x ≡ y)
      → (ap f p)⁻¹ ≡ ap f (p ⁻¹)
ap-⁻¹ f (refl x) = refl (refl (f x))

-- Lemma 2.2.2 iii)
ap-∘ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
       (f : A → B) (g : B → C) {x y : A} (p : x ≡ y)
     → ap (g ∘ f) p ≡ (ap g ∘ ap f) p
ap-∘ f g (refl x) = refl (refl (g (f x)))

-- Lemma 2.2.2 iv)
ap-id : {A : 𝒰 𝒾} {x y : A} (p : x ≡ y)
      → ap id p ≡ p
ap-id (refl x) = refl (refl x)

-- Some more helpers
ap-const : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {a₁ a₂ : A}
           (p : a₁ ≡ a₂) (c : B)
         → ap (λ _ → c) p ≡ refl c
ap-const (refl _) c = refl _

∙-left-cancel : {A : 𝒰 𝒾} {x y z : A}
                (p : x ≡ y) {q r : y ≡ z}
              → p ∙ q ≡ p ∙ r
              → q ≡ r
∙-left-cancel p {q} {r} path = begin
  q              ≡˘⟨ refl-left ⟩
  refl _ ∙ q     ≡˘⟨ ap (_∙ q) (⁻¹-left∙ p) ⟩
  (p ⁻¹ ∙ p) ∙ q ≡⟨ ∙-assoc (p ⁻¹) ⟩
  p ⁻¹ ∙ (p ∙ q) ≡⟨ ap ((p ⁻¹) ∙_) path ⟩
  p ⁻¹ ∙ (p ∙ r) ≡˘⟨ ∙-assoc (p ⁻¹) ⟩
  (p ⁻¹ ∙ p) ∙ r ≡⟨ ap (_∙ r) (⁻¹-left∙ p) ⟩
  refl _ ∙ r     ≡⟨ refl-left ⟩
  r ∎

∙-right-cancel : {A : 𝒰 𝒾} {x y z : A}
                 (p : x ≡ y) {q : x ≡ y} {r : y ≡ z}
               → p ∙ r ≡ q ∙ r
               → p ≡ q
∙-right-cancel p {q} {r} path = begin
  p              ≡˘⟨ refl-right ⟩
  p ∙ refl _     ≡˘⟨ ap (p ∙_) (⁻¹-right∙ r) ⟩
  p ∙ (r ∙ r ⁻¹) ≡˘⟨ ∙-assoc p ⟩
  (p ∙ r) ∙ r ⁻¹ ≡⟨ ap (_∙ (r ⁻¹)) path ⟩
  (q ∙ r) ∙ r ⁻¹ ≡⟨ ∙-assoc q ⟩
  q ∙ (r ∙ r ⁻¹) ≡⟨ ap (q ∙_) (⁻¹-right∙ r) ⟩
  q ∙ refl _     ≡⟨ refl-right ⟩
  q ∎
```

## Section 2.3 Type families are fibrations

```agda
-- Lemma 2.3.1.
tr : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿) {x y : A}
          → x ≡ y → P x → P y
tr P (refl x) = id

-- Lemma 2.3.2.
lift : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿}
       {x y : A} (u : P x) (p : x ≡ y)
     → ((x , u) ≡ (y , tr P p u))
lift u (refl x) = refl (x , u)

-- Lemma 2.3.4.
apd : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} (f : (x : A) → P x) {x y : A}
      (p : x ≡ y) → tr P p (f x) ≡ f y
apd f (refl x) = refl (f x)

-- Lemma 2.3.5.
trconst : {A : 𝒰 𝒾} (B : 𝒰 𝒿) {x y : A}
          (p : x ≡ y) (b : B)
        → tr (λ - → B) p b ≡ b
trconst B (refl x) b = refl b

-- Lemma 2.3.8.
apd-trconst : {A : 𝒰 𝒾} (B : 𝒰 𝒿) {x y : A}
              (f : A → B)
              (p : x ≡ y)
            → apd f p ≡ trconst B p (f x) ∙ ap f p
apd-trconst B f (refl x) = refl (refl (f x))

-- Lemma 2.3.9.
-- (Slight generalization for the ≡-𝒰-∙ proof)
tr-∘ : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿) {x y z : A}
       (p : x ≡ y) (q : y ≡ z)
     → (tr P q) ∘ (tr P p) ≡ tr P (p ∙ q)
tr-∘ P (refl x) (refl x) = refl id

-- Lemma 2.3.10.
tr-ap : {A : 𝒰 𝒾} (B : A → 𝒰 𝒿) (f : A → A)
        {x y : A} (p : x ≡ y)
      → tr (B ∘ f) p ≡ tr B (ap f p)
tr-ap B f (refl _) = refl _

-- A slight generalization of the above lemma
tr-ap' : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (P : A → 𝒰 𝓀) (f : B → A)
         {x y : B} (p : x ≡ y)
       → tr (P ∘ f) p ≡ tr P (ap f p)
tr-ap' P f (refl _) = refl _

-- A related result
tr-ap-assoc : {A : 𝒰 𝒾} (B : A → 𝒰 𝒿) {x y : A}
              (p : x ≡ y)
            → tr (id ∘ B) p ≡ tr id (ap B p)
tr-ap-assoc B (refl _) = refl _

```

## Section 2.4 Homotopies and equivalences

```agda
_∼_ : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} → Π P → Π P → 𝒰 (𝒾 ⊔ 𝒿)
f ∼ g = ∀ x → f x ≡ g x

∼-refl : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} (f : Π P) → (f ∼ f)
∼-refl f = λ x → (refl (f x))

∼-sym : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿}
      → (f g : Π P)
      → (f ∼ g)
      → (g ∼ f)
∼-sym f g H = λ x → (H x)⁻¹

∼-trans : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿}
        → (f g h : Π P)
        → (f ∼ g)
        → (g ∼ h)
        → (f ∼ h)
∼-trans f g h H1 H2 = λ x → (H1 x) ∙ (H2 x)

-- Lemma 2.4.3.
∼-naturality : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
               (f g : A → B) (H : f ∼ g) {x y : A} {p : x ≡ y}
             → H x ∙ ap g p ≡ ap f p ∙ H y
∼-naturality f g H {x} {_} {refl a} = refl-right ∙ refl-left ⁻¹

-- Corollary 2.4.4.
~-id-naturality : {A : 𝒰 𝒾}
                  (f : A → A) (H : f ∼ id) {x : A}
                → (H (f x)) ≡ (ap f (H x))
~-id-naturality f H {x} = begin
    H (f x)                             ≡˘⟨ refl-right ⟩
    H (f x) ∙ (refl (f x))              ≡˘⟨ i ⟩
    H (f x) ∙ (H x ∙ (H x)⁻¹)           ≡˘⟨ ∙-assoc (H (f x)) ⟩
    (H (f x) ∙ H x) ∙ (H x)⁻¹           ≡˘⟨ ii ⟩
    (H (f x) ∙ (ap id (H x))) ∙ (H x)⁻¹ ≡⟨ iii ⟩
    (ap f (H x) ∙ (H x)) ∙ (H x)⁻¹      ≡⟨ ∙-assoc (ap f (H x)) ⟩
    ap f (H x) ∙ ((H x) ∙ (H x)⁻¹)      ≡⟨ iv ⟩
    ap f (H x) ∙ (refl (f x))           ≡⟨ refl-right ⟩
    ap f (H x) ∎
  where
    i = ap (H (f x) ∙_) (⁻¹-right∙ (H x))
    ii = ap (λ - → (H (f x) ∙ (-)) ∙ (H x)⁻¹) (ap-id (H x))
    iii = ap (_∙ (H x)⁻¹) (∼-naturality f id H)
    iv = ap (ap f (H x) ∙_) (⁻¹-right∙ (H x))

-- Definition 2.4.6.
isQinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → B) → 𝒰 (𝒾 ⊔ 𝒿)
isQinv f = Σ g ꞉ (codomain f → domain f) , (f ∘ g ∼ id) × (g ∘ f ∼ id)

-- Example 2.4.7.
isQinv-id : (A : 𝒰 𝒾) → isQinv (𝑖𝑑 A)
isQinv-id A = (𝑖𝑑 A) , refl , refl

-- Example 2.4.8.
isQinv-∙─ : {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y)
          → isQinv (λ (- : y ≡ z) → p ∙ -)
isQinv-∙─ p =
  (λ - → p ⁻¹ ∙ -) ,
  (λ q → (∙-assoc p)⁻¹ ∙ ap (_∙ q) (⁻¹-right∙ p) ∙ refl-left) ,
  (λ q → (∙-assoc (p ⁻¹))⁻¹ ∙ ap (_∙ q) (⁻¹-left∙ p) ∙ refl-left)

isQinv-─∙ : {A : 𝒰 𝒾} {x y z : A} (p : x ≡ y)
          → isQinv (λ (- : z ≡ x) → - ∙ p)
isQinv-─∙ p =
  (λ - → - ∙ p ⁻¹) ,
  (λ q → (∙-assoc q) ∙ ap (q ∙_) (⁻¹-left∙ p) ∙ refl-right) ,
  (λ q → (∙-assoc q) ∙ ap (q ∙_) (⁻¹-right∙ p) ∙ refl-right)

-- Definition 2.4.10.
isEquiv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → B) → 𝒰 (𝒾 ⊔ 𝒿)
isEquiv f = (Σ g ꞉ (codomain f → domain f) , (f ∘ g ∼ id))
           × (Σ h ꞉ (codomain f → domain f) , (h ∘ f ∼ id))

invs⇒equivs : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B)
            → (isQinv f) → (isEquiv f)
invs⇒equivs f ( g , α , β ) = ( (g , α) , (g , β) )

equivs⇒invs : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B)
            → (isEquiv f) → (isQinv f)
equivs⇒invs f ( (g , α) , (h , β) ) = ( g , α , β' )
  where
    γ : (x : codomain f) → (g x ≡ h x)
    γ x = begin
      g x ≡˘⟨ β (g x) ⟩
      h (f (g x)) ≡⟨ ap h (α x) ⟩
      h x ∎
    β' : g ∘ f ∼ 𝑖𝑑 (domain f)
    β' x = γ (f x) ∙ β x

-- Definition 2.4.11.
_≃_ : 𝒰 𝒾 → 𝒰 𝒿 → 𝒰 (𝒾 ⊔ 𝒿)
A ≃ B = Σ f ꞉ (A → B), isEquiv f

-- Helpers to get the quasi-inverse data from an equiv
≃-→ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → A ≃ B → (A → B)
≃-→ (f , eqv) = f

≃-← : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → A ≃ B → (B → A)
≃-← (f , eqv) =
 let (g , ε , η) = equivs⇒invs f eqv
  in g

≃-ε : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
    → (equiv : (A ≃ B))
    → ((≃-→ equiv) ∘ (≃-← equiv) ∼ id)
≃-ε (f , eqv) =
 let (g , ε , η) = equivs⇒invs f eqv
  in ε

≃-η : {A : 𝒰 𝒾} {B : 𝒰 𝒿}
    → (equiv : (A ≃ B))
    → ((≃-← equiv) ∘ (≃-→ equiv) ∼ id)
≃-η (f , eqv) =
 let (g , ε , η) = equivs⇒invs f eqv
  in η

-- Lemma 2.4.12. i)
≃-refl : (A : 𝒰 𝒾) → A ≃ A
≃-refl A = ( 𝑖𝑑 A , invs⇒equivs (𝑖𝑑 A) (isQinv-id A) )

-- Lemma 2.4.12. ii)
≃-sym : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → A ≃ B → B ≃ A
≃-sym ( f , e ) =
  let ( f⁻¹ , p , q) = ( equivs⇒invs f e )
  in  ( f⁻¹ , invs⇒equivs f⁻¹ (f , q , p) )

-- Lemma 2.4.12. iii)
≃-trans : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
        → A ≃ B → B ≃ C → A ≃ C
≃-trans eqvf@( f , ef ) eqvg@( g , eg ) =
  let ( f⁻¹ , pf , qf ) = ( equivs⇒invs f ef )
      ( g⁻¹ , pg , qg ) = ( equivs⇒invs g eg )
      h1 : (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) ∼ id
      h1 x = begin
        g (f (f⁻¹ (g⁻¹ x))) ≡⟨ ap g (pf (g⁻¹ x)) ⟩
        g (g⁻¹ x)           ≡⟨ pg x ⟩
        x ∎
      h2 : (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ∼ id
      h2 x = begin
        f⁻¹ (g⁻¹ (g (f x))) ≡⟨ ap f⁻¹ (qg (f x)) ⟩
        f⁻¹ (f x)           ≡⟨ qf x ⟩
        x ∎
  in  ((g ∘ f) , invs⇒equivs (g ∘ f) ((f⁻¹ ∘ g⁻¹) , h1 , h2))

_≃∙_ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
      → A ≃ B → B ≃ C → A ≃ C
eqv1 ≃∙ eqv2 = ≃-trans eqv1 eqv2
infixl 30 _≃∙_
```

## 2.5 The higher groupoid structure of type formers

## 2.6 Cartesian product types

```agda
pair×⁼⁻¹ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {w w' : A × B}
        → (w ≡ w') → ((pr₁ w ≡ pr₁ w') × (pr₂ w ≡ pr₂ w'))
pair×⁼⁻¹ p = (ap pr₁ p , ap pr₂ p)

-- Theorem 2.6.2
pair×⁼ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {w w' : A × B}
        → ((pr₁ w ≡ pr₁ w') × (pr₂ w ≡ pr₂ w')) → (w ≡ w')
pair×⁼ (refl w1 , refl w2) = refl (w1 , w2)

≡-×-≃ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {w w' : A × B}
      → (w ≡ w') ≃ ((pr₁ w ≡ pr₁ w') × (pr₂ w ≡ pr₂ w'))
≡-×-≃ {𝒾} {𝒿} {A} {B} {w1 , w2} {w'1 , w'2} =
  pair×⁼⁻¹ , invs⇒equivs pair×⁼⁻¹ (pair×⁼ , α , β)
    where
      α : (pq : (w1 ≡ w'1) × (w2 ≡ w'2))
        → pair×⁼⁻¹ (pair×⁼ pq) ≡ pq
      α (refl w1 , refl w2) = refl (refl w1 , refl w2)
      β : (p : (w1 , w2 ≡ w'1 , w'2))
        → pair×⁼ (pair×⁼⁻¹ p) ≡ p
      β (refl (w1 , w2)) = refl (refl (w1 , w2))

-- Propositional uniqueness principle for products
×-uniq : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (z : A × B)
       → z ≡ (pr₁ z , pr₂ z)
×-uniq z = pair×⁼ (refl (pr₁ z) , refl (pr₂ z))

-- Propositional uniqueness principle for paths in products
≡-×-uniq : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {x y : A × B}
         → (r : x ≡ y)
         → r ≡ pair×⁼(ap pr₁ r , ap pr₂ r)
≡-×-uniq r = (≃-η ≡-×-≃ r)⁻¹

≡-×-⁻¹ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {x₁ y₁ : A} {x₂ y₂ : B}
       → (p : x₁ ≡ y₁)
       → (q : x₂ ≡ y₂)
       → pair×⁼((p ⁻¹) , (q ⁻¹)) ≡ (pair×⁼(p , q) ⁻¹)
≡-×-⁻¹ (refl _) (refl _) = refl _

≡-×-∙ : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {x₁ y₁ z₁ : A} {x₂ y₂ z₂ : B}
      → (p : x₁ ≡ y₁)
      → (q : y₁ ≡ z₁)
      → (p' : x₂ ≡ y₂)
      → (q' : y₂ ≡ z₂)
      → pair×⁼((p ∙ q) , (p' ∙ q')) ≡ pair×⁼(p , p') ∙ pair×⁼(q , q')
≡-×-∙ (refl _) (refl _) (refl _) (refl _) = refl _

-- Theorem 2.6.4.
tr-× : (Z : 𝒰 𝒾) (A : Z → 𝒰 𝒿) (B : Z → 𝒰 𝓀)
        (z w : Z) (p : z ≡ w) (x : A z × B z)
      → tr (λ - → A - × B -) p x ≡ (tr A p (pr₁ x) , tr B p (pr₂ x))
tr-× Z A B z w (refl z) x = ×-uniq x
```

## 2.7 Σ-types

I'm using a slightly different definition of the `f` in the following
theorem, as it'll be useful further on.

```agda
pair⁼⁻¹₁ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {w w' : Σ B}
         → (p : w ≡ w') → (pr₁ w) ≡ (pr₁ w')
pair⁼⁻¹₁ p = ap pr₁ p

pair⁼⁻¹₂ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {w w' : Σ B}
         → (p : w ≡ w') → tr B (ap pr₁ p) (pr₂ w) ≡ (pr₂ w')
pair⁼⁻¹₂ (refl w) = refl _

-- Theorem 2.7.2.
pair⁼⁻¹ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {w w' : Σ B}
        → (w ≡ w') → (Σ p ꞉ (pr₁ w ≡ pr₁ w') , tr B p (pr₂ w) ≡ (pr₂ w'))
pair⁼⁻¹ p = (pair⁼⁻¹₁ p , pair⁼⁻¹₂ p)

pair⁼ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {w w' : Σ B}
      → (Σ p ꞉ (pr₁ w ≡ pr₁ w') , tr B p (pr₂ w) ≡ (pr₂ w')) → (w ≡ w')
pair⁼ (refl w1 , refl w2) = refl (w1 , w2)

≡-Σ-≃ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} (w w' : Σ B)
      → (w ≡ w') ≃ (Σ p ꞉ (pr₁ w ≡ pr₁ w') , tr B p (pr₂ w) ≡ (pr₂ w'))
≡-Σ-≃ {𝒾} {𝒿} {A} {B} (w1 , w2) (w'1 , w'2) =
  pair⁼⁻¹ , invs⇒equivs pair⁼⁻¹ (pair⁼ , α , β)
    where
      α : (pq : (Σ p ꞉ w1 ≡ w'1 , tr B p w2 ≡ w'2))
        → pair⁼⁻¹ (pair⁼ pq) ≡ pq
      α (refl w1 , refl w2) = refl (refl w1 , refl w2)
      β : (p : (w1 , w2 ≡ w'1 , w'2))
        → pair⁼ (pair⁼⁻¹ p) ≡ p
      β (refl (w1 , w2)) = refl (refl (w1 , w2))

-- Corollary 2.7.3.
Σ-uniq : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} (z : Σ P)
       → z ≡ (pr₁ z , pr₂ z)
Σ-uniq z = pair⁼ (refl _ , refl _)

-- Propositional uniqueness principle for paths in dependent sums
≡-Σ-uniq : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {x y : Σ B}
         → (r : x ≡ y)
         → r ≡ pair⁼(pair⁼⁻¹ r)
≡-Σ-uniq r = (≃-η (≡-Σ-≃ _ _) r)⁻¹

-- Other lemmas
≡-Σ-comp₁ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {w w' : Σ B}
            (p : pr₁ w ≡ pr₁ w') (q : tr B p (pr₂ w) ≡ pr₂ w')
          → pair⁼⁻¹₁ (pair⁼(p , q)) ≡ p
≡-Σ-comp₁ (refl _) (refl _) = refl _

≡-Σ-comp₂ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {w w' : Σ B}
            (p : pr₁ w ≡ pr₁ w') (q : tr B p (pr₂ w) ≡ pr₂ w')
          → pair⁼⁻¹₂ (pair⁼(p , q)) ≡
              ap (λ - → tr B - (pr₂ w)) (≡-Σ-comp₁ p q) ∙ q
≡-Σ-comp₂ (refl _) (refl _) = refl _
```

## 2.8 The unit type

```agda
-- Theorem 2.8.1.
≡-𝟙-≃ : (x y : 𝟙) → (x ≡ y) ≃ 𝟙
≡-𝟙-≃ ⋆ ⋆ = f , invs⇒equivs f (g , α , β)
  where
    f : ⋆ ≡ ⋆ → 𝟙
    f p = ⋆
    g : 𝟙 → ⋆ ≡ ⋆
    g ⋆ = refl ⋆
    α : (p : 𝟙) → f (g p) ≡ p
    α ⋆ = refl ⋆
    β : (p : ⋆ ≡ ⋆) → g (f p) ≡ p
    β (refl ⋆) = refl (refl ⋆)

-- Any to elements of 𝟙 are equal
isProp-𝟙 : (x y : 𝟙) → (x ≡ y)
isProp-𝟙 x y =
  let (f , ((g , f-g) , (h , h-f))) = ≡-𝟙-≃ x y
   in h ⋆
```

## 2.9 Π-types and the function extensionality axiom

```agda
happly : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {f g : Π B}
       → f ≡ g → f ∼ g
happly p x = ap (λ - → - x) p

-- Axiom 2.9.3.
postulate funext-ax : {𝒾 𝒿 : Level} {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} (f g : Π B)
                    → isEquiv (happly {𝒾} {𝒿} {A} {B} {f} {g})

≡-Π-≃ : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿}
        (f g : Π B)
      → (f ≡ g) ≃ (f ∼ g)
≡-Π-≃ f g = happly , funext-ax f g

funext : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿}
       → {f g : Π B}
       → f ∼ g → f ≡ g
funext {f = f} {g = g} = ≃-← (≡-Π-≃ f g)

-- Slightly generalized
≡-Π-comp : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿}
         → {f g : Π B}
         → (h : f ∼ g)
         → happly (funext h) ≡ h
≡-Π-comp {f = f} {g = g} = ≃-ε (≡-Π-≃ f g)

≡-Π-uniq : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿}
         → {f g : Π B}
         → (p : f ≡ g)

         → p ≡ funext (happly p)
≡-Π-uniq {f = f} {g = g} p = (≃-η (≡-Π-≃ f g) p)⁻¹

tr-→ : {X : 𝒰 𝒾} {A : X → 𝒰 𝒿} {B : X → 𝒰 𝓀}
       {x₁ x₂ : X} (p : x₁ ≡ x₂) (f : A x₁ → B x₁)
     → tr (λ x → (A x → B x)) p f ≡ (λ x → tr B p (f (tr A (p ⁻¹) x)))
tr-→ (refl x₁) f = refl f

tr-Π : {X : 𝒰 𝒾}
       {A : X → 𝒰 𝓀}
       {B : (x : X) → A x → 𝒰 𝒿}
       {x₁ x₂ : X} (p : x₁ ≡ x₂)
       (f : (a : A x₁) → B x₁ a)
       (a : A x₂)
     → (tr (λ (x : X) → ((a : A x) → B x a)) p f a) ≡
         (tr (λ (w : Σ A) → B (pr₁ w) (pr₂ w))
             (pair⁼( (p ⁻¹) , refl _ ) ⁻¹) (f (tr A (p ⁻¹) a)))
tr-Π (refl _) f a = refl _

-- Lemma 2.9.6.
≡-tr-Π-≃ : {X : 𝒰 𝒾}
           {A : X → 𝒰 𝓀}
           {B : X → 𝒰 𝒿}
           {x y : X} (p : x ≡ y)
           (f : A x → B x)
           (g : A y → B y)
         → (tr (λ z → A z → B z) p f ≡ g)
             ≃ ((a : A x) → tr B p (f a) ≡ g (tr A p a))
≡-tr-Π-≃ (refl x) f g = ≡-Π-≃ f g
```

## 2.10 Universes and the univalence axiom

```agda
-- Lemma 2.10.1.
idtoeqv : {A B : 𝒰 𝒾} → A ≡ B → A ≃ B
idtoeqv {𝒾} {A} {B} p = tr (λ C → C) p , helper p
  where
    helper : (p : A ≡ B) → isEquiv (tr (λ C → C) p)
    helper (refl A) = invs⇒equivs (𝑖𝑑 A) (isQinv-id A)

postulate ua-ax : {𝒾 : Level} → (A B : 𝒰 𝒾) → isEquiv (idtoeqv {𝒾} {A} {B})

≡-𝒰-≃ : (A B : 𝒰 𝒾) → (A ≡ B) ≃ (A ≃ B)
≡-𝒰-≃ A B = idtoeqv , ua-ax A B

ua : {A B : 𝒰 𝒾} → A ≃ B → A ≡ B
ua {𝒾} {A} {B} eqv = ≃-← (≡-𝒰-≃ A B) eqv

≡-𝒰-comp : {A B : 𝒰 𝒾} (eqv : A ≃ B) (x : A)
        → tr id (ua eqv) x ≡ ≃-→ eqv x
≡-𝒰-comp {A = A} {B = B} eqv x =
 happly q x
  where
   p : idtoeqv (ua eqv) ≡ eqv
   p = ≃-ε (≡-𝒰-≃ A B) eqv
   q : tr id (ua eqv) ≡ pr₁ eqv
   q = ap pr₁ p

≡-𝒰-uniq : {A B : 𝒰 𝒾} (p : A ≡ B)
        → p ≡ ua (idtoeqv p)
≡-𝒰-uniq {A = A} {B = B} p = (≃-η (≡-𝒰-≃ A B) p)⁻¹

ua-id : {A : 𝒰 𝒾}
      → refl A ≡ ua (≃-refl A)
ua-id {A = A} = begin
  refl A                ≡⟨ ≡-𝒰-uniq (refl A) ⟩
  ua (idtoeqv (refl A)) ≡⟨⟩
  ua (≃-refl A)         ∎

≡-𝒰-∙ : {A B C : 𝒰 𝒾} (eqvf : A ≃ B) (eqvg : B ≃ C)
     → ua eqvf ∙ ua eqvg ≡ ua (≃-trans eqvf eqvg)
≡-𝒰-∙ {𝒾} {A} {B} {C} eqvf eqvg = begin
  ua eqvf ∙ ua eqvg                    ≡⟨ ≡-𝒰-uniq (p ∙ q)                ⟩
  ua (idtoeqv (p ∙ q))                 ≡˘⟨ ap (λ - → ua -) idtoeqv-∙      ⟩
  ua (≃-trans (idtoeqv p) (idtoeqv q)) ≡˘⟨ ap (λ - → ua
                                               (≃-trans (idtoeqv p) -))
                                               ((≃-ε (≡-𝒰-≃ B C) eqvg)⁻¹) ⟩
  ua (≃-trans (idtoeqv p) eqvg)        ≡˘⟨ ap (λ - → ua (≃-trans - eqvg))
                                              ((≃-ε (≡-𝒰-≃ A B) eqvf)⁻¹)  ⟩
  ua (≃-trans eqvf eqvg)               ∎
 where
  p = ua eqvf
  q = ua eqvg

  idtoeqv-∙ : ≃-trans (idtoeqv p) (idtoeqv q) ≡ idtoeqv (p ∙ q)
  idtoeqv-∙ = begin
     ≃-trans (idtoeqv p) (idtoeqv q)           ≡⟨⟩
     ≃-trans (tr id p , pr₂ (idtoeqv p))
       (tr id q , pr₂ (idtoeqv q))             ≡⟨⟩
     ((tr id q) ∘ (tr id p) ,
       pr₂ (≃-trans (idtoeqv p) (idtoeqv q)))  ≡⟨ pair⁼((tr-∘ id p q) ,
                                                        (lemma p q)) ⟩
     (tr id (p ∙ q) , pr₂ (idtoeqv (p ∙ q)))   ≡⟨⟩
     idtoeqv (p ∙ q)                           ∎
    where
     lemma : (p : A ≡ B) (q : B ≡ C)
           → tr isEquiv (tr-∘ id p q)
              (pr₂ (≃-trans (idtoeqv p) (idtoeqv q)))
             ≡ pr₂ (idtoeqv (p ∙ q))
     lemma (refl A) (refl A) = refl _

-- Lemma for next theorem
tr-_∼id : {A : 𝒰 𝒾} {f : A → A}
        → (h : f ∼ id)
        → tr (_∼ id) (funext h) h ≡ refl
tr-_∼id {𝒾} {A} {f} h = begin
  tr (_∼ id) (funext h) h                     ≡⟨ i ⟩
  tr (_∼ id) (funext (happly (funext h))) h   ≡⟨ ii ⟩
  tr (_∼ id) (funext (happly (funext h)))
     (happly (funext h))                      ≡⟨ iii (funext h) ⟩
  refl ∎
 where
  i = ap (λ - → tr (_∼ id) (funext -) h) (≡-Π-comp h)⁻¹
  ii = ap (λ - → tr (_∼ id) (funext (happly (funext h))) -)
           (≡-Π-comp h)⁻¹
  iii : (p : f ≡ id) → tr (_∼ id) (funext (happly p)) (happly p) ≡ refl
  iii (refl f) = ap (λ - → tr (_∼ id) - (happly (refl f)))
                     (≡-Π-uniq (refl f))⁻¹

ua⁻¹ : {A B : 𝒰 𝒾} (eqv : A ≃ B)
     → (ua eqv)⁻¹ ≡ ua (≃-sym eqv)
ua⁻¹ {𝒾} {A} {B} eqvf@(f , e) =
  sufficient (≡-𝒰-∙ eqvf⁻¹ eqvf ∙ claim2)
 where
  p = ua eqvf
  eqvf⁻¹ = ≃-sym eqvf
  f⁻¹ = pr₁ eqvf⁻¹
  q = ua eqvf⁻¹

  sufficient : (ua eqvf⁻¹ ∙ ua eqvf ≡ refl B)
             → (ua eqvf)⁻¹ ≡ ua eqvf⁻¹
  sufficient p = begin
   (ua eqvf)⁻¹                          ≡˘⟨ refl-left ⟩
   refl B ∙ (ua eqvf)⁻¹                 ≡⟨ ap (_∙ (ua eqvf)⁻¹) (p ⁻¹) ⟩
   (ua eqvf⁻¹ ∙ ua eqvf) ∙ (ua eqvf)⁻¹  ≡⟨ ∙-assoc (ua eqvf⁻¹)        ⟩
   ua eqvf⁻¹ ∙ (ua eqvf ∙ (ua eqvf)⁻¹)  ≡⟨ ap (ua eqvf⁻¹ ∙_)
                                              (⁻¹-right∙ (ua eqvf))   ⟩
   ua eqvf⁻¹ ∙ refl A                   ≡⟨ refl-right                 ⟩
   ua eqvf⁻¹                            ∎

  claim1 : ≃-trans eqvf⁻¹ eqvf ≡ ≃-refl B
  claim1 = pair⁼ (i , ii)
   where
    i : (f ∘ f⁻¹) ≡ id
    i = funext (≃-η eqvf⁻¹)
    id-equiv : isEquiv id
    id-equiv = tr isEquiv i (pr₂ (≃-trans eqvf⁻¹ (f , e)))
    g h : B → B
    g = pr₁ (pr₁ id-equiv)
    h = pr₁ (pr₂ id-equiv)
    α = pr₂ (pr₁ id-equiv)
    β = pr₂ (pr₂ id-equiv)

    ii : ((g , α) , (h , β)) ≡ ((id , refl) , (id , refl))
    ii = pair×⁼(pair⁼(iia , iib) , pair⁼(iic , iid))
     where
      iia : g ≡ id
      iia = funext α
      iib : tr (_∼ id) iia α ≡ refl
      iib = tr-_∼id α
      iic : h ≡ id
      iic = funext β
      iid : tr (_∼ id) iic β ≡ refl
      iid = tr-_∼id β

  claim2 : ua (≃-trans eqvf⁻¹ eqvf) ≡ refl B
  claim2 = ap (ua) claim1 ∙ ((≡-𝒰-uniq (refl B))⁻¹)
```

## 2.11 Identity type

```agda
-- Lemma 2.11.1.
isEquiv⇒isEquiv-ap :
             {A : 𝒰 𝒾} {B : 𝒰 𝒾}
           → (f : A → B)
           → isEquiv f
           → (a a' : A)
           → isEquiv (ap f {a} {a'})
isEquiv⇒isEquiv-ap f e a a' =
  invs⇒equivs (ap f) (inv-apf , ε , η )
 where
  f⁻¹ = pr₁ (equivs⇒invs f e)
  α = pr₁ (pr₂ (equivs⇒invs f e))
  β = pr₂ (pr₂ (equivs⇒invs f e))
  inv-apf : (f a ≡ f a') → (a ≡ a')
  inv-apf p = (β a)⁻¹ ∙ (ap f⁻¹ p) ∙ β a'
  η = λ p → begin
    (β a)⁻¹ ∙ (ap f⁻¹ (ap f p)) ∙ β a'  ≡˘⟨ ap (λ - → (β a)⁻¹ ∙ - ∙ β a')
                                               (ap-∘ f f⁻¹ p) ⟩
    (β a)⁻¹ ∙ (ap (f⁻¹ ∘ f) p) ∙ β a'   ≡⟨ ∙-assoc ((β a)⁻¹) ⟩
    (β a)⁻¹ ∙ ((ap (f⁻¹ ∘ f) p) ∙ β a') ≡˘⟨ ap ((β a)⁻¹ ∙_) (∼-naturality _ _ β) ⟩
    (β a)⁻¹ ∙ (β a ∙ ap id p)           ≡˘⟨ ∙-assoc ((β a)⁻¹) ⟩
    ((β a)⁻¹ ∙ β a) ∙ ap id p           ≡⟨ ap (_∙ ap id p) (⁻¹-left∙ (β a)) ⟩
    refl _ ∙ ap id p                    ≡⟨ refl-left ⟩
    ap id p                             ≡⟨ ap-id p ⟩
    p ∎
  ε : (ap f) ∘ (inv-apf) ∼ id
  ε q = begin
    ap f ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')                                ≡˘⟨ i ⟩
    refl _ ∙ ap f ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')                       ≡˘⟨ ii ⟩
    (α (f a))⁻¹ ∙ α (f a) ∙ ap f ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')        ≡⟨ iii ⟩
    (α (f a))⁻¹ ∙ (α (f a) ∙ ap f ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a'))      ≡˘⟨ iv ⟩
    (α (f a))⁻¹ ∙
      (α (f a) ∙ ap id (ap f ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')))          ≡⟨ v ⟩
    (α (f a))⁻¹ ∙
      (ap (f ∘ f⁻¹) (ap f ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')) ∙ α (f a'))  ≡⟨ vi ⟩
    (α (f a))⁻¹ ∙
      (ap f (ap f⁻¹ (ap f ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a'))) ∙ α (f a')) ≡˘⟨ vii ⟩
    (α (f a))⁻¹ ∙
      (ap f (ap (f⁻¹ ∘ f) ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')) ∙ α (f a'))  ≡˘⟨ viii ⟩
    (α (f a))⁻¹ ∙ (ap f (ap (f⁻¹ ∘ f)
      ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a') ∙ refl _) ∙ α (f a'))             ≡˘⟨ ix ⟩
    (α (f a))⁻¹ ∙ (ap f (ap (f⁻¹ ∘ f) ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')
      ∙ (β a' ∙ ((β a')⁻¹))) ∙ α (f a'))                              ≡˘⟨ x ⟩
    (α (f a))⁻¹ ∙ (ap f ((ap (f⁻¹ ∘ f) ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')
      ∙ β a') ∙ ((β a')⁻¹)) ∙ α (f a'))                               ≡˘⟨ xi ⟩
    (α (f a))⁻¹ ∙ (ap f (β a ∙ ap id ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')
      ∙ ((β a')⁻¹)) ∙ α (f a'))                                       ≡⟨ xii ⟩
    (α (f a))⁻¹ ∙ (ap f (β a ∙ ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a')
      ∙ ((β a')⁻¹)) ∙ α (f a'))                                       ≡˘⟨ xiii ⟩
    (α (f a))⁻¹ ∙ (ap f (β a ∙ ((β a)⁻¹ ∙ (ap f⁻¹ q)) ∙ β a'
      ∙ ((β a')⁻¹)) ∙ α (f a'))                                       ≡˘⟨ xiv ⟩
    (α (f a))⁻¹ ∙ (ap f (β a ∙ (β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a'
      ∙ ((β a')⁻¹)) ∙ α (f a'))                                       ≡⟨ xv ⟩
    (α (f a))⁻¹ ∙
      (ap f (refl _ ∙ (ap f⁻¹ q) ∙ β a' ∙ ((β a')⁻¹)) ∙ α (f a'))     ≡⟨ xvi ⟩
    (α (f a))⁻¹ ∙ (ap f ((ap f⁻¹ q) ∙ β a' ∙ ((β a')⁻¹)) ∙ α (f a'))  ≡⟨ xvii ⟩
    (α (f a))⁻¹ ∙
      (ap f ((ap f⁻¹ q) ∙ (β a' ∙ ((β a')⁻¹))) ∙ α (f a'))            ≡⟨ xviii ⟩
    (α (f a))⁻¹ ∙ (ap f ((ap f⁻¹ q) ∙ refl _) ∙ α (f a'))             ≡⟨ xix ⟩
    (α (f a))⁻¹ ∙ (ap f (ap f⁻¹ q) ∙ α (f a'))                        ≡˘⟨ xx ⟩
    (α (f a))⁻¹ ∙ (ap (f ∘ f⁻¹) q ∙ α (f a'))                         ≡˘⟨ xxi ⟩
    (α (f a))⁻¹ ∙ (α (f a ) ∙ ap id q)                                ≡⟨ xxii ⟩
    (α (f a))⁻¹ ∙ (α (f a ) ∙ q)                                      ≡˘⟨ xxiii ⟩
    (α (f a))⁻¹ ∙ α (f a ) ∙ q                                        ≡⟨ xxiv ⟩
    refl _ ∙ q                                                        ≡⟨ xxv ⟩
    q                                                                 ∎
     where
      i     = refl-left
      ii    = ap (λ - → - ∙ ap f ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a'))
                 (⁻¹-left∙ (α (f a)))
      iii   = ∙-assoc ((α (f a))⁻¹)
      iv    = ap (λ - → (α (f a))⁻¹ ∙ (α (f a) ∙ -)) (ap-id _)
      v     = ap ((α (f a))⁻¹ ∙_) (∼-naturality (f ∘ f⁻¹) id α)
      vi    = ap (λ - → (α (f a))⁻¹ ∙ (- ∙ α (f a'))) (ap-∘ f⁻¹ f _)
      vii   = ap (λ - → (α (f a))⁻¹ ∙ (ap f - ∙ α (f a'))) (ap-∘ f f⁻¹ _)
      viii  = ap (λ - → (α (f a))⁻¹ ∙ (ap f - ∙ α (f a'))) refl-right
      ix    = ap (λ - → (α (f a))⁻¹ ∙ (ap f (ap (f⁻¹ ∘ f)
                 ((β a)⁻¹ ∙ (ap f⁻¹ q) ∙ β a') ∙ -) ∙ α (f a')))
                 (⁻¹-right∙ (β a'))
      x     = ap (λ - → (α (f a))⁻¹ ∙ (ap f - ∙ α (f a'))) (∙-assoc _)
      xi    = ap (λ - → (α (f a))⁻¹ ∙ (ap f (- ∙ ((β a')⁻¹)) ∙ α (f a')))
                 (∼-naturality _ _ β)
      xii   = ap (λ - → (α (f a))⁻¹ ∙
                 (ap f (β a ∙ - ∙ ((β a')⁻¹)) ∙ α (f a'))) (ap-id _)
      xiii  = ap (λ - → (α (f a))⁻¹ ∙
                 (ap f (- ∙ ((β a')⁻¹)) ∙ α (f a'))) (∙-assoc (β a))
      xiv   = ap (λ - → (α (f a))⁻¹ ∙
                 (ap f (- ∙ β a' ∙ ((β a')⁻¹)) ∙ α (f a'))) (∙-assoc (β a))
      xv    = ap (λ - → (α (f a))⁻¹ ∙ (ap f (- ∙ (ap f⁻¹ q) ∙ β a' ∙ ((β a')⁻¹))
                 ∙ α (f a'))) (⁻¹-right∙ (β a))
      xvi   = ap (λ - → (α (f a))⁻¹ ∙ (ap f (- ∙ β a' ∙ ((β a')⁻¹)) ∙ α (f a')))
                 refl-left
      xvii  = ap (λ - → (α (f a))⁻¹ ∙ (ap f - ∙ α (f a'))) (∙-assoc _)
      xviii = ap (λ - → (α (f a))⁻¹ ∙ (ap f ((ap f⁻¹ q) ∙ -) ∙ α (f a')))
                 (⁻¹-right∙ (β a'))
      xix   = ap (λ - → (α (f a))⁻¹ ∙ (ap f - ∙ α (f a'))) (refl-right)
      xx    = ap (λ - → (α (f a))⁻¹ ∙ (- ∙ α (f a'))) (ap-∘ _ _ q)
      xxi   = ap ((α (f a))⁻¹ ∙_) (∼-naturality (f ∘ f⁻¹) id α)
      xxii  = ap (λ - → (α (f a))⁻¹ ∙ (α (f a ) ∙ -)) (ap-id q)
      xxiii = ∙-assoc _
      xxiv  = ap (_∙ q) (⁻¹-left∙ (α (f a)))
      xxv   = refl-left

-- Lemma 2.11.2.
tr-Homc─ : {A : 𝒰 𝒾} (a : A) {x₁ x₂ : A} (p : x₁ ≡ x₂) (q : a ≡ x₁)
         → tr (λ x → a ≡ x) p q ≡ q ∙ p
tr-Homc─ a (refl _) (refl _) = refl-right ⁻¹

tr-Hom─c : {A : 𝒰 𝒾} (a : A) {x₁ x₂ : A} (p : x₁ ≡ x₂) (q : x₁ ≡ a)
         → tr (λ x → x ≡ a) p q ≡ p ⁻¹ ∙ q
tr-Hom─c a (refl _) (refl _) = refl-right ⁻¹

tr-Hom── : {A : 𝒰 𝒾} {x₁ x₂ : A} (p : x₁ ≡ x₂) (q : x₁ ≡ x₁)
         → tr (λ x → x ≡ x) p q ≡ p ⁻¹ ∙ q ∙ p
tr-Hom── (refl _) q = (ap (_∙ refl _) refl-left ∙ refl-right) ⁻¹

-- Theorem 2.11.3.
tr-fx≡gx : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f g : A → B) {a a' : A}
           (p : a ≡ a') (q : f a ≡ g a)
         → tr (λ x → f x ≡ g x) p q ≡ (ap f p)⁻¹ ∙ q ∙ (ap g p)
tr-fx≡gx f g (refl a) q = (refl-left)⁻¹ ∙ (refl-right)⁻¹

-- Theorem 2.11.5.
tr-x≡x-≃ : {A : 𝒰 𝒾} {a a' : A}
           (p : a ≡ a') (q : a ≡ a) (r : a' ≡ a')
         → (tr (λ x → x ≡ x) p q ≡ r) ≃ (q ∙ p ≡ p ∙ r)
tr-x≡x-≃ {𝒾} {A} {a} {a'} (refl a) q r =
  map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map : q ≡ r → (q ∙ refl a ≡ refl a ∙ r)
  map eq = refl-right ∙ eq ∙ (refl-left)⁻¹
  map⁻¹ : (q ∙ refl a ≡ refl a ∙ r) → (q ≡ r)
  map⁻¹ eq' = (refl-right)⁻¹ ∙ eq' ∙ refl-left
  ε : map ∘ map⁻¹ ∼ id
  ε eq' = begin
    refl-right ∙ ((refl-right)⁻¹ ∙ eq' ∙ refl-left) ∙ (refl-left)⁻¹ ≡˘⟨ i ⟩
    refl-right ∙ ((refl-right)⁻¹ ∙ eq') ∙ refl-left ∙ (refl-left)⁻¹ ≡˘⟨ ii ⟩
    refl-right ∙ (refl-right)⁻¹ ∙ eq' ∙ refl-left ∙ (refl-left)⁻¹   ≡⟨ iii ⟩
    refl _ ∙ eq' ∙ refl-left ∙ (refl-left)⁻¹                        ≡⟨ iv ⟩
    eq' ∙ refl-left ∙ (refl-left)⁻¹                                 ≡⟨ v ⟩
    eq' ∙ (refl-left ∙ (refl-left)⁻¹)                               ≡⟨ vi ⟩
    eq' ∙ refl _                                                    ≡⟨ vii ⟩
    eq' ∎
   where
    i   = ap (_∙ (refl-left)⁻¹) (∙-assoc refl-right)
    ii  = ap (λ - → - ∙ refl-left ∙ (refl-left)⁻¹) (∙-assoc refl-right)
    iii = ap (λ - → - ∙ eq' ∙ refl-left ∙ (refl-left)⁻¹) (⁻¹-right∙ refl-right)
    iv  = ap (λ - → - ∙ refl-left ∙ (refl-left)⁻¹) refl-left
    v   = ∙-assoc eq'
    vi  = ap (eq' ∙_) (⁻¹-right∙ refl-left)
    vii = refl-right
  η : map⁻¹ ∘ map ∼ id
  η eq = begin
    (refl-right)⁻¹ ∙ (refl-right ∙ eq ∙ (refl-left)⁻¹) ∙ refl-left ≡˘⟨ i ⟩
    (refl-right)⁻¹ ∙ (refl-right ∙ eq) ∙ (refl-left)⁻¹ ∙ refl-left ≡˘⟨ ii ⟩
    (refl-right)⁻¹ ∙ refl-right ∙ eq ∙ (refl-left)⁻¹ ∙ refl-left   ≡⟨ iii ⟩
    refl _ ∙ eq ∙ (refl-left)⁻¹ ∙ refl-left                        ≡⟨ iv ⟩
    eq ∙ (refl-left)⁻¹ ∙ refl-left                                 ≡⟨ v ⟩
    eq ∙ ((refl-left)⁻¹ ∙ refl-left)                               ≡⟨ vi ⟩
    eq ∙ refl _                                                    ≡⟨ vii ⟩
    eq ∎
   where
    i   = ap (_∙ refl-left) (∙-assoc ((refl-right)⁻¹))
    ii  = ap (λ - → - ∙ (refl-left)⁻¹ ∙ refl-left) (∙-assoc ((refl-right)⁻¹))
    iii = ap (λ - → - ∙ eq ∙ (refl-left)⁻¹ ∙ refl-left) (⁻¹-left∙ refl-right)
    iv  = ap (λ - → - ∙ (refl-left)⁻¹ ∙ refl-left) refl-left
    v   = ∙-assoc eq
    vi  = ap (eq ∙_) (⁻¹-left∙ refl-left)
    vii = refl-right
```

## 2.12 Coproducts

```agda
𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 p = tr id p ⋆

₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝒰 lzero
  f ₀ = 𝟘
  f ₁ = 𝟙
  q : 𝟙 ≡ 𝟘
  q = ap f p
```

# 2.13 Naturals

```agda
code-ℕ : ℕ → ℕ → 𝒰₀
code-ℕ 0 0               = 𝟙
code-ℕ (succ m) 0        = 𝟘
code-ℕ 0 (succ m)        = 𝟘
code-ℕ (succ m) (succ n) = code-ℕ m n

r-ℕ : (n : ℕ) → code-ℕ n n
r-ℕ 0        = ⋆
r-ℕ (succ n) = r-ℕ n

-- Theorem 2.13.1.
encode-ℕ : (m n : ℕ) → (m ≡ n) → code-ℕ m n
encode-ℕ m n p = tr (code-ℕ m) p (r-ℕ m)

decode-ℕ : (m n : ℕ) → code-ℕ m n → (m ≡ n)
decode-ℕ 0 0 f = refl 0
decode-ℕ (succ m) 0 f = !𝟘 (succ m ≡ 0) f
decode-ℕ 0 (succ n) f = !𝟘 (0 ≡ succ n) f
decode-ℕ (succ m) (succ n) f = ap succ (decode-ℕ m n f)

decode∘encode-ℕ∼id : (m n : ℕ) → (decode-ℕ m n) ∘ (encode-ℕ m n) ∼ id
decode∘encode-ℕ∼id m n (refl n) = lema n
  where
    lema : (n : ℕ) → decode-ℕ n n (r-ℕ n) ≡ refl n
    lema 0 = refl _
    lema (succ n) = ap (ap succ) (lema n)

encode∘decode-ℕ∼id : (m n : ℕ) → (encode-ℕ m n) ∘ (decode-ℕ m n) ∼ id
encode∘decode-ℕ∼id 0 0 ⋆               = refl ⋆
encode∘decode-ℕ∼id (succ m) 0 c        = !𝟘 _ c
encode∘decode-ℕ∼id 0 (succ n) c        = !𝟘 _ c
encode∘decode-ℕ∼id (succ m) (succ n) c = begin
  encode-ℕ (succ m) (succ n) (decode-ℕ (succ m) (succ n) c)           ≡⟨⟩
  encode-ℕ (succ m) (succ n) (ap succ (decode-ℕ m n c))               ≡⟨⟩
  tr (code-ℕ (succ m)) (ap succ (decode-ℕ m n c)) (r-ℕ (succ m))      ≡⟨ i ⟩
  tr (λ - → code-ℕ (succ m) (succ -)) (decode-ℕ m n c) (r-ℕ (succ m)) ≡⟨⟩
  tr (λ - → code-ℕ (succ m) (succ -)) (decode-ℕ m n c) (r-ℕ m)        ≡⟨⟩
  tr (code-ℕ m) (decode-ℕ m n c) (r-ℕ m)                              ≡⟨⟩
  encode-ℕ m n (decode-ℕ m n c)                                       ≡⟨ ii ⟩
  c ∎
 where
  i = happly (tr-ap (code-ℕ (succ m)) succ ((decode-ℕ m n c)) ⁻¹) (r-ℕ (succ m))
  ii = encode∘decode-ℕ∼id m n c

≡-ℕ-≃ : (m n : ℕ) → (m ≡ n) ≃ code-ℕ m n
≡-ℕ-≃ m n =
  encode-ℕ m n , invs⇒equivs (encode-ℕ m n)
    (decode-ℕ m n , encode∘decode-ℕ∼id m n , decode∘encode-ℕ∼id m n)

-- Equation 2.13.2.
¬succ≡0 : (m : ℕ) → ¬(succ m ≡ 0)
¬succ≡0 m = encode-ℕ (succ m) 0

¬0≡succ : (m : ℕ) → ¬(0 ≡ succ m)
¬0≡succ m = encode-ℕ 0 (succ m)

-- Equation 2.13.3.
sm≡sn⇒m≡n : {m n : ℕ} → (succ m ≡ succ n) → (m ≡ n)
sm≡sn⇒m≡n {m} {n} p = decode-ℕ m n (encode-ℕ (succ m) (succ n) p)
```

## 2.15 Universal properties

```agda
-- Theorem 2.15.7.
ΠΣ-comm : {X : 𝒰 𝒾} {A : X → 𝒰 𝒿} {P : (x : X) → A x → 𝒰 𝓀}
        → ((x : X) → Σ a ꞉ (A x) , P x a)
           ≃ (Σ g ꞉ ((x : X) → A x) , ((x : X) → P x (g x)))
ΠΣ-comm {𝒾} {𝒿} {𝓀} {X} {A} {P} = map , invs⇒equivs map (map⁻¹ , ε , η)
  where
    map : ((x : X) → Σ a ꞉ (A x) , P x a)
        → (Σ g ꞉ ((x : X) → A x) , ((x : X) → P x (g x)))
    map f = (λ x → pr₁ (f x)) , (λ x → pr₂ (f x))
    map⁻¹ : (Σ g ꞉ ((x : X) → A x) , ((x : X) → P x (g x)))
          → ((x : X) → Σ a ꞉ (A x) , P x a)
    map⁻¹ (g , h) = λ x → (g x , h x)
    ε : map ∘ map⁻¹ ∼ id
    ε (g , h) = refl _
    η : map⁻¹ ∘ map ∼ id
    η f = funext (λ x → (Σ-uniq (f x))⁻¹)
```

## Additional commentaries

Univalence let us prove something like path induction but for equivalences.
```agda
ind-≃ : (P : (A B : 𝒰 𝒾) → (A ≃ B) → 𝒰 𝒿)
   → ((A : 𝒰 𝒾) → P A A (≃-refl A))
   → (A B : 𝒰 𝒾) → (e : A ≃ B) → P A B e
ind-≃ P f A B e =
 tr (λ (C , e') → P A C e')
    (tr (λ - → A , ≃-refl A ≡ B , -) (≃-ε (≡-𝒰-≃ A B) e) (lemma (ua e)))
    (f A)
  where
    lemma : (p : A ≡ B) → (A , ≃-refl A) ≡ (B , ≃-→ (≡-𝒰-≃ A B) p)
    lemma (refl A) = pair⁼(refl _ , refl _)
```

Also `×` is commutative in the following sense
```agda
×-comm : (A : 𝒰 𝒾) (B : 𝒰 𝒿) → A × B ≃ B × A
×-comm A B = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = λ (x , y) → (y , x)
  map⁻¹ = λ (y , x) → (x , y)
  ε = refl
  η = refl
```

It associates with `Σ` in the sense that: (see also Exercise 2.10)
```agda
Σ-×-assoc : (A : 𝒰 𝒾) (P : A → 𝒰 𝒿) (Q : 𝒰 𝓀)
          → (Σ x ꞉ A , P x × Q) ≃ ((Σ x ꞉ A , P x) × Q)
Σ-×-assoc A P Q = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = λ (x , y , z) → ((x , y) , z)
  map⁻¹ = λ ((x , y) , z) → (x , y , z)
  ε = refl
  η = refl
```

`Σ` commutes with itself in the sense that
```agda
Σ-comm : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (P : A → B → 𝒰 𝓀)
       → (Σ x ꞉ A , Σ y ꞉ B , P x y) ≃ (Σ y ꞉ B , Σ x ꞉ A , P x y)
Σ-comm P = map , invs⇒equivs map (map⁻¹ , ε , η)
 where
  map = λ (x , y , z) → (y , x , z)
  map⁻¹ = λ (y , x , z) → (x , y , z)
  ε = refl
  η = refl
```

Since we don't have cumulativity we'll use the fact that `raise` is a equivalence.

```agda
raise⁻¹ : (𝒿 : Level) (A : 𝒰 𝒾) → Raised 𝒿 A → A
raise⁻¹ 𝒿 A (raise x) = x

≡-Raised-≃ : (𝒿 : Level) (A : 𝒰 𝒾) → Raised 𝒿 A ≃ A
≡-Raised-≃ 𝒿 A =
  (raise⁻¹ 𝒿 A) , invs⇒equivs (raise⁻¹ 𝒿 A) (raise , refl , η)
 where
  η : raise ∘ (raise⁻¹ 𝒿 A) ∼ id
  η (raise x) = refl (raise x)
```
