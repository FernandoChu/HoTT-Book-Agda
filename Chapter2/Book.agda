{-# OPTIONS --without-K --exact-split --safe --auto-inline --no-import-sorts #-}

module Chapter2.Book where

open import Chapter1.Book public
open import Chapter1.Exercises public

---------------------------------------------------------------------------------

-- Section 2.1 Types are higher groupoids

_⁻¹ : {X : 𝒰 𝒾} → {x y : X} → x ≡ y → y ≡ x
(refl x)⁻¹ = refl x
infix  40 _⁻¹

_∙_ : {X : 𝒰 𝒾} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
(refl x) ∙ (refl x) = (refl x)
infixl 30 _∙_

-- Lemma 2.1.4 i)
refl-left : {X : 𝒰 𝒾} {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : 𝒰 𝒾} {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {refl x} = refl (refl x)

-- Lemma 2.1.4 ii)
⁻¹-left∙ : {X : 𝒰 𝒾} {x y : X} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {X : 𝒰 𝒾} {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)

-- Lemma 2.1.4 iii)
⁻¹-involutive : {X : 𝒰 𝒾} {x y : X} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)

-- Lemma 2.1.4 iv)
∙-assoc : {X : 𝒰 𝒾} {x y z t : X} (p : x ≡ y) {q : y ≡ z} {r : z ≡ t}
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc (refl x) {refl x} {refl x} = refl (refl x)

-- Common ≡ reasoning helpers from
-- https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#2708

begin_ : {X : 𝒰 𝒾} {x y : X} → x ≡ y → x ≡ y
begin_ x≡y = x≡y
infix  1 begin_

_≡⟨⟩_ : {X : 𝒰 𝒾} (x {y} : X) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

step-≡ : {X : 𝒰 𝒾} (x {y z} : X) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = x≡y ∙ y≡z
syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

step-≡˘ : {X : 𝒰 𝒾} (x {y z} : X) → y ≡ z → y ≡ x → x ≡ z
step-≡˘ _ y≡z y≡x = (y≡x)⁻¹ ∙ y≡z
syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
infixr 2 _≡⟨⟩_ step-≡ step-≡˘

_∎ : {X : 𝒰 𝒾} (x : X) → x ≡ x
_∎ x = refl x
infix  3 _∎

---------------------------------------------------------------------------------

-- Section 2.2 Functions are functors

ap : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} (refl x) = refl (f x)

-- Lemma 2.2.2 i)
ap-∙ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y) {x y z : X}
       (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f (refl x) (refl x) = refl (refl (f x))

-- Lemma 2.2.2 ii)
ap⁻¹ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y) {x y : X} (p : x ≡ y)
     → (ap f p)⁻¹ ≡ ap f (p ⁻¹)
ap⁻¹ f (refl x) = refl (refl (f x))

-- Lemma 2.2.2 iii)
ap-∘ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {Z : 𝒰 𝓀}
       (f : X → Y) (g : Y → Z) {x y : X} (p : x ≡ y)
     → ap (g ∘ f) p ≡ (ap g ∘ ap f) p
ap-∘ f g (refl x) = refl (refl (g (f x)))

-- Lemma 2.2.2 iv)
ap-id : {X : 𝒰 𝒾} {x y : X} (p : x ≡ y)
      → ap id p ≡ p
ap-id (refl x) = refl (refl x)

---------------------------------------------------------------------------------

-- Section 2.3 Type families are fibrations

tr : {X : 𝒰 𝒾} (A : X → 𝒰 𝒿) {x y : X}
          → x ≡ y → A x → A y
tr A (refl x) = id

lift : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿}
       {x y : A} (u : P x) (p : x ≡ y)
     → ((x , u) ≡ (y , tr P p u))
lift u (refl x) = refl (x , u)

apd : {X : 𝒰 𝒾} {A : X → 𝒰 𝒿} (f : (x : X) → A x) {x y : X}
      (p : x ≡ y) → tr A p (f x) ≡ f y
apd f (refl x) = refl (f x)

-- Lemma 2.3.9
-- (Slight generalization for the ua-∘ proof)
tr-tr : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} {x y z : A}
       (p : x ≡ y) (q : y ≡ z)
     → (tr P q) ∘ (tr P p) ≡ tr P (p ∙ q)
tr-tr (refl x) (refl x) = refl id

---------------------------------------------------------------------------------

-- Section 2.4 Homotopies and equivalences

_∼_ : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿} → Π P → Π P → 𝒰 (𝒾 ⊔ 𝒿)
f ∼ g = ∀ x → f x ≡ g x

∼-refl : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿} (f : Π P) → (f ∼ f)
∼-refl f = λ x → (refl (f x))

∼-sym : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿}
      → (f g : Π P)
      → (f ∼ g)
      → (g ∼ f)
∼-sym f g H = λ x → (H x)⁻¹

∼-trans : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿}
        → (f g h : Π P)
        → (f ∼ g)
        → (g ∼ h)
        → (f ∼ h)
∼-trans f g h H1 H2 = λ x → (H1 x) ∙ (H2 x)

-- Lemma 2.4.3
∼-naturality : {X : 𝒰 𝒾} {A : 𝒰 𝒿}
               (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
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
    ap f (H x) ∙ (refl (f x)) ≡⟨ refl-right ⟩
    ap f (H x) ∎
  where
    i = ap (H (f x) ∙_) (⁻¹-right∙ (H x))
    ii = ap (λ - → (H (f x) ∙ (-)) ∙ (H x)⁻¹) (ap-id (H x))
    iii = ap (_∙ (H x)⁻¹) (∼-naturality f id H)
    iv = ap (ap f (H x) ∙_) (⁻¹-right∙ (H x))


qinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → B) → 𝒰 (𝒾 ⊔ 𝒿)
qinv f = Σ g ꞉ (codomain f → domain f) , (f ∘ g ∼ id) × (g ∘ f ∼ id)

-- Example 2.4.7.
qinv-id-id : (A : 𝒰 𝒾) → qinv (𝑖𝑑 A)
qinv-id-id A = (𝑖𝑑 A) , refl , refl

is-equiv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → B) → 𝒰 (𝒾 ⊔ 𝒿)
is-equiv f = (Σ g ꞉ (codomain f → domain f) , (f ∘ g ∼ id))
           × (Σ h ꞉ (codomain f → domain f) , (h ∘ f ∼ id))

invs-are-equivs : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B)
                → (qinv f) → (is-equiv f)
invs-are-equivs f ( g , α , β ) = ( (g , α) , (g , β) )

equivs-are-invs : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B)
                → (is-equiv f) → (qinv f)
equivs-are-invs f ( (g , α) , (h , β) ) = ( g , α , β' )
  where
    A = domain f
    B = codomain f
    γ : (x : B) → (g x ≡ h x)
    γ x = begin
      g x ≡˘⟨ β (g x) ⟩
      h (f (g x)) ≡⟨ ap h (α x) ⟩
      h x ∎
    β' : g ∘ f ∼ 𝑖𝑑 A
    β' x = γ (f x) ∙ β x

_≃_ : 𝒰 𝒾 → 𝒰 𝒿 → 𝒰 (𝒾 ⊔ 𝒿)
A ≃ B = Σ f ꞉ (A → B), is-equiv f

Eq→fun ⌜_⌝ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ≃ Y → X → Y
Eq→fun (f , i) = f
⌜_⌝            = Eq→fun

Eq→fun-is-equiv ⌜⌝-is-equiv : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (e : X ≃ Y) → is-equiv (⌜ e ⌝)
Eq→fun-is-equiv (f , i) = i
⌜⌝-is-equiv             = Eq→fun-is-equiv

-- Lemma 2.4.12 i)
≃-refl : (X : 𝒰 𝒾) → X ≃ X
≃-refl X = ( 𝑖𝑑 X , invs-are-equivs (𝑖𝑑 X) (qinv-id-id X) )

-- Lemma 2.4.12 ii)
≃-sym : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ≃ Y → Y ≃ X
≃-sym ( f , e ) =
  let ( f⁻¹ , p , q) = ( equivs-are-invs f e )
  in  ( f⁻¹ , invs-are-equivs f⁻¹ (f , q , p) )

-- Lemma 2.4.12 iii)
≃-trans-helper : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
                 (eqvf : A ≃ B) (eqvg : B ≃ C)
               → is-equiv (pr₁ eqvg ∘ pr₁ eqvf)
≃-trans-helper ( f , ef ) ( g , eg ) =
  let ( f⁻¹ , pf , qf ) = ( equivs-are-invs f ef )
      ( g⁻¹ , pg , qg ) = ( equivs-are-invs g eg )
      h1 : ((g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) ∼ id)
      h1 x = begin
        g (f (f⁻¹ (g⁻¹ x))) ≡⟨ ap g (pf (g⁻¹ x)) ⟩
        g (g⁻¹ x) ≡⟨ pg x ⟩
        x ∎
      h2 : ((f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ∼ id)
      h2 x = begin
        f⁻¹ (g⁻¹ (g (f x))) ≡⟨ ap f⁻¹ (qg (f x)) ⟩
        f⁻¹ (f x) ≡⟨ qf x ⟩
        x ∎
  in  invs-are-equivs (g ∘ f) ((f⁻¹ ∘ g⁻¹) , h1 , h2)

≃-trans : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
        → A ≃ B → B ≃ C → A ≃ C
≃-trans eqvf@( f , ef ) eqvg@( g , eg ) =
  let ( f⁻¹ , pf , qf ) = ( equivs-are-invs f ef )
      ( g⁻¹ , pg , qg ) = ( equivs-are-invs g eg )
      h1 : ((g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) ∼ id)
      h1 x = begin
        g (f (f⁻¹ (g⁻¹ x))) ≡⟨ ap g (pf (g⁻¹ x)) ⟩
        g (g⁻¹ x)           ≡⟨ pg x ⟩
        x ∎
      h2 : ((f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ∼ id)
      h2 x = begin
        f⁻¹ (g⁻¹ (g (f x))) ≡⟨ ap f⁻¹ (qg (f x)) ⟩
        f⁻¹ (f x)           ≡⟨ qf x ⟩
        x ∎
  in  ( (g ∘ f) , ≃-trans-helper eqvf eqvg )

---------------------------------------------------------------------------------

-- 2.5 The higher groupoid structure of type formers

---------------------------------------------------------------------------------

-- 2.6 Cartesian product types

pair×⁼⁻¹ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {w w' : X × Y}
        → (w ≡ w') → ((pr₁ w ≡ pr₁ w') × (pr₂ w ≡ pr₂ w'))
pair×⁼⁻¹ (refl w) = ( refl (pr₁ w) , refl (pr₂ w) )

pair×⁼ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {w w' : X × Y}
        → ((pr₁ w ≡ pr₁ w') × (pr₂ w ≡ pr₂ w')) → (w ≡ w')
pair×⁼ {𝒾} {𝒿} {X} {Y} {w1 , w2} {w'1 , w'2} (refl w1 , refl w2) = refl (w1 , w2)

-- Theorem 2.6.2
×-≡-≃ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {w w' : X × Y}
      → (w ≡ w') ≃ ((pr₁ w ≡ pr₁ w') × (pr₂ w ≡ pr₂ w'))
×-≡-≃ {𝒾} {𝒿} {X} {Y} {w1 , w2} {w'1 , w'2} =
  pair×⁼⁻¹ , invs-are-equivs pair×⁼⁻¹ (pair×⁼ , α , β)
    where
      α : (pq : (w1 ≡ w'1) × (w2 ≡ w'2))
        → pair×⁼⁻¹ (pair×⁼ pq) ≡ pq
      α (refl w1 , refl w2) = refl (refl w1 , refl w2)
      β : (p : (w1 , w2 ≡ w'1 , w'2))
        → pair×⁼ (pair×⁼⁻¹ p) ≡ p
      β (refl (w1 , w2)) = refl (refl (w1 , w2))

×-uniq : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {z : X × Y}
       → z ≡ (pr₁ z , pr₂ z)
×-uniq {𝒾} {𝒿} {X} {Y} {z} = pair×⁼ (refl (pr₁ z) , refl (pr₂ z))

trA×B : (Z : 𝒰 𝒾) (A : Z → 𝒰 𝒿) (B : Z → 𝒰 𝓀)
        (z w : Z) (p : z ≡ w) (x : A z × B z)
      → tr (λ - → A - × B -) p x ≡ (tr A p (pr₁ x) , tr B p (pr₂ x))
trA×B Z A B z w (refl z) x = ×-uniq

---------------------------------------------------------------------------------

-- 2.7 Σ-types

pair⁼⁻¹ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} {w w' : Σ Y}
        → (w ≡ w') → (Σ p ꞉ (pr₁ w ≡ pr₁ w') , tr Y p (pr₂ w) ≡ (pr₂ w'))
pair⁼⁻¹ (refl w) = ( refl (pr₁ w) , refl (pr₂ w) )

pair⁼ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} {w w' : Σ Y}
        → (Σ p ꞉ (pr₁ w ≡ pr₁ w') , tr Y p (pr₂ w) ≡ (pr₂ w')) → (w ≡ w')
pair⁼ {𝒾} {𝒿} {X} {Y} {w1 , w2} {w'1 , w'2} (refl w1 , refl w2) = refl (w1 , w2)

Σ-≡-≃ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} {w w' : Σ Y}
      → (w ≡ w') ≃ (Σ p ꞉ (pr₁ w ≡ pr₁ w') , tr Y p (pr₂ w) ≡ (pr₂ w'))
Σ-≡-≃ {𝒾} {𝒿} {X} {Y} {w1 , w2} {w'1 , w'2} =
  pair⁼⁻¹ , invs-are-equivs pair⁼⁻¹ (pair⁼ , α , β)
    where
      α : (pq : (Σ p ꞉ w1 ≡ w'1 , tr Y p w2 ≡ w'2))
        → pair⁼⁻¹ (pair⁼ pq) ≡ pq
      α (refl w1 , refl w2) = refl (refl w1 , refl w2)
      β : (p : (w1 , w2 ≡ w'1 , w'2))
        → pair⁼ (pair⁼⁻¹ p) ≡ p
      β (refl (w1 , w2)) = refl (refl (w1 , w2))

---------------------------------------------------------------------------------

-- 2.8 The unit type

𝟙-≡-≃ : (x y : 𝟙) → (x ≡ y) ≃ 𝟙
𝟙-≡-≃ ⋆ ⋆ = f , invs-are-equivs f (g , α , β)
  where
    f : ⋆ ≡ ⋆ → 𝟙
    f p = ⋆
    g : 𝟙 → ⋆ ≡ ⋆
    g ⋆ = refl ⋆
    α : (p : 𝟙) → f (g p) ≡ p
    α ⋆ = refl ⋆
    β : (p : ⋆ ≡ ⋆) → g (f p) ≡ p
    β (refl ⋆) = refl (refl ⋆)

𝟙-is-subsingleton : (x y : 𝟙) → (x ≡ y)
𝟙-is-subsingleton x y =
  let (f , ((g , f-g) , (h , h-f))) = 𝟙-≡-≃ x y
   in h ⋆

---------------------------------------------------------------------------------

-- 2.9 Π-types and the function extensionality axiom

happly : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {f g : Π B} → f ≡ g → f ∼ g
happly p x = ap (λ - → - x) p

has-funext : (𝒾 𝒿 : Level) → 𝒰 ((𝒾 ⊔ 𝒿)⁺)
has-funext 𝒾 𝒿 = {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} (f g : Π B)
               → is-equiv (happly {𝒾} {𝒿} {A} {B} {f} {g})

qinv-fe : has-funext 𝒾 𝒿 → {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} (f g : Π B) → qinv happly
qinv-fe fe f g = equivs-are-invs happly (fe f g)

funext : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} → has-funext 𝒾 𝒿 → {f g : Π B} → f ∼ g → f ≡ g
funext fe {f} {g} htpy =
  let (funext , _ , _ ) = qinv-fe fe f g
   in funext htpy

tr-f : (X : 𝒰 𝒾) (A : X → 𝒰 𝒿) (B : X → 𝒰 𝓀)
      (x₁ x₂ : X) (p : x₁ ≡ x₂) (f : A x₁ → B x₁)
    → tr (λ x → (A x → B x)) p f ≡ (λ x → tr B p (f (tr A (p ⁻¹) x)))
tr-f X A B x₁ x₂ (refl x₁) f = refl f

---------------------------------------------------------------------------------

-- 2.10 Universes and the univalence axiom

Id→Eq : (X Y : 𝒰 𝒾) → X ≡ Y → X ≃ Y
Id→Eq X X (refl X) = 𝑖𝑑 X , invs-are-equivs (𝑖𝑑 X) (qinv-id-id X)

-- Workaround : I need this helper to delay the pattern match in `idtoeqv`,
-- while still being able to use this same function in other places, like in
-- the construction of `ua-∘`.
idtoeqv-helper : {X Y : 𝒰 𝒾} (p : X ≡ Y) → is-equiv (tr (λ C → C) p)
idtoeqv-helper (refl X) = invs-are-equivs (𝑖𝑑 X) (qinv-id-id X)

idtoeqv : {X Y : 𝒰 𝒾} → X ≡ Y → X ≃ Y
idtoeqv {𝒾} {X} {Y} p = tr (λ C → C) p , (idtoeqv-helper p)

is-univalent : (𝒾 : Level) → 𝒰 (𝒾 ⁺)
is-univalent 𝒾 = (X Y : 𝒰 𝒾) → is-equiv (idtoeqv {𝒾} {X} {Y})

qinv-ua : is-univalent 𝒾 → (X Y : 𝒰 𝒾) → qinv idtoeqv
qinv-ua ua X Y = equivs-are-invs idtoeqv (ua X Y)

ua : is-univalent 𝒾 → {X Y : 𝒰 𝒾} → X ≃ Y → X ≡ Y
ua u {X} {Y} eqv =
  let (ua , idtoeqv∘ua , ua∘idtoeqv) = qinv-ua u X Y
   in ua eqv

-- Helper
id∼idtoeqv∘ua : (u : is-univalent 𝒾)
              → {X Y : 𝒰 𝒾} (eqv : X ≃ Y)
              → eqv ≡ idtoeqv (ua u eqv)
id∼idtoeqv∘ua u {X} {Y} eqv =
  let (ua , idtoeqv∘ua , ua∘idtoeqv) = qinv-ua u X Y
   in (idtoeqv∘ua eqv)⁻¹

≡u-comp : (u : is-univalent 𝒾)
        → {X Y : 𝒰 𝒾} (eqv : X ≃ Y) (x : X)
        → tr (λ C → C) (ua u eqv) x ≡ pr₁ eqv x
≡u-comp u {X} {Y} eqv x =
 happly q x
  where
   p : idtoeqv (ua u eqv) ≡ eqv
   p = (id∼idtoeqv∘ua u eqv)⁻¹
   q : tr (λ C → C) (ua u eqv) ≡ pr₁ eqv
   q = ap pr₁ p

≡u-uniq : (u : is-univalent 𝒾)
        → {X Y : 𝒰 𝒾} (p : X ≡ Y)
        → p ≡ ua u (idtoeqv p)
≡u-uniq u {X} {Y} p =
  let (ua , idtoeqv∘ua , ua∘idtoeqv) = qinv-ua u X Y
   in (ua∘idtoeqv p)⁻¹


ua-id : (u : is-univalent 𝒾)
      → {A : 𝒰 𝒾}
      → refl A ≡ ua u (≃-refl A)
ua-id u {A} = begin
  refl A                  ≡⟨ ≡u-uniq u (refl A) ⟩
  ua u (idtoeqv (refl A)) ≡⟨⟩
  ua u (≃-refl A)         ∎

-- ua-∘ : (u : is-univalent 𝒾)
--      → {X Y Z : 𝒰 𝒾} (eqvf : X ≃ Y) (eqvg : Y ≃ Z)
--      → ua u eqvf ∙ ua u eqvg ≡ ua u (≃-trans eqvf eqvg)
-- ua-∘ u {X} {Y} {Z} eqvf eqvg = proof ⁻¹
--  where
--   p : X ≡ Y
--   p = ua u eqvf
--   q : Y ≡ Z
--   q = ua u eqvg
--   x : (p : X ≡ Y) → is-equiv (tr (λ C → C) p)
--   x (refl X) = invs-are-equivs (𝑖𝑑 X) (qinv-id-id X)
--   a : idtoeqv p ≡ tr (λ C → C) p , idtoeqv-helper p
--   a = refl _
--   lemma' : ≃-trans (idtoeqv p) (idtoeqv q) ≡ idtoeqv (p ∙ q)
--   lemma' = begin
--      ≃-trans (idtoeqv p) (idtoeqv q) ≡⟨⟩
--      ≃-trans (tr (λ C → C) p , idtoeqv-helper p)
--        (tr (λ C → C) q , idtoeqv-helper q) ≡⟨⟩
--      ((tr (λ C → C) q) ∘ (tr (λ C → C) p) , ≃-trans-helper (idtoeqv p) (idtoeqv q)) ≡⟨ pair⁼((trtr p q) , refl _) ⟩
--      (tr (λ C → C) (p ∙ q) , tr (λ - → is-equiv -) (trtr p q) (≃-trans-helper (idtoeqv p) (idtoeqv q)) ) ≡⟨ pair⁼(refl _ , _) ⟩
--      (tr (λ C → C) (p ∙ q) , idtoeqv-helper (p ∙ q)) ≡⟨⟩
--      idtoeqv (p ∙ q) ∎
--     where
--      zz : (tr (λ C → C) q) ∘ (tr (λ C → C) p) ≡ tr (λ C → C) (p ∙ q)
--      zz = trtr p q

--   -- lemma : (p : X ≡ Y) (q : Y ≡ Z)
--   --       → ≃-trans (idtoeqv p) (idtoeqv q) ≡ idtoeqv (p ∙ q)
--   -- lemma (refl X) (refl Y) = x
--   --  where
--   --   x : ≃-trans (≃-refl X) (≃-refl X) ≡
--   --         idtoeqv (refl X ∙ refl X)
--   --   x = begin
--   --    ≃-trans (≃-refl X) (≃-refl X) ≡⟨ _ ⟩
--   --    id , _ ≡⟨⟩
--   --    idtoeqv (refl X) ≡⟨⟩
--   --    idtoeqv (refl X ∙ refl X) ∎
--   proof : ua u (≃-trans eqvf eqvg) ≡ ua u eqvf ∙ ua u eqvg
--   proof = begin
--    ua u (≃-trans eqvf eqvg)               ≡⟨ ap (λ - → ua u (≃-trans - eqvg))
--                                                (id∼idtoeqv∘ua u eqvf)         ⟩
--    ua u (≃-trans (idtoeqv p) eqvg)        ≡⟨ ap (λ - → ua u
--                                                 (≃-trans (idtoeqv p) -))
--                                                (id∼idtoeqv∘ua u eqvg)         ⟩
--    ua u (≃-trans (idtoeqv p) (idtoeqv q)) ≡⟨ ap (λ - → ua u -) (lemma') ⟩
--    ua u (idtoeqv (p ∙ q))                 ≡˘⟨ ≡u-uniq u (p ∙ q) ⟩
--    ua u eqvf ∙ ua u eqvg                  ∎

-- ua⁻¹ : (u : is-univalent 𝒾)
--      → {X Y : 𝒰 𝒾} (eqv : X ≃ Y)
--      → (ua u eqv)⁻¹ ≡ ua u (≃-sym eqv)
-- ua⁻¹ u eqv = _

-- Note: Univalence could be expressed like this
Univalence : 𝓤ω
Univalence = ∀ i → is-univalent i

---------------------------------------------------------------------------------

-- 2.11 Identity type

-- Lemma 2.11.2.
trHomc- : {A : 𝒰 𝒾} (a x₁ x₂ : A) (p : x₁ ≡ x₂) (q : a ≡ x₁)
          → tr (λ x → a ≡ x) p q ≡ q ∙ p
trHomc- a x₁ x₂ (refl x₁) (refl x₁) = refl-right ⁻¹

trHom-c : {A : 𝒰 𝒾} (a x₁ x₂ : A) (p : x₁ ≡ x₂) (q : x₁ ≡ a)
          → tr (λ x → x ≡ a) p q ≡ p ⁻¹ ∙ q
trHom-c a x₁ x₂ (refl x₁) (refl x₁) = refl-right ⁻¹

-- Theorem 2.11.3.
tr-fx≡gx : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f g : A → B) {a a' : A}
           (p : a ≡ a') (q : f a ≡ g a)
         → tr (λ x → f x ≡ g x) p q ≡ (ap f p)⁻¹ ∙ q ∙ (ap g p)
tr-fx≡gx f g (refl a) q = (refl-left)⁻¹ ∙ (refl-right)⁻¹

---------------------------------------------------------------------------------

-- 2.12 Coproducts

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
