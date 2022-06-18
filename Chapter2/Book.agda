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
syntax step-≡  x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

step-≡˘ : {X : 𝒰 𝒾} (x {y z} : X) → y ≡ z → y ≡ x → x ≡ z
step-≡˘ _ y≡z y≡x = (y≡x)⁻¹ ∙ y≡z
syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
infixr 2 _≡⟨⟩_ step-≡ step-≡˘

_∎ : {X : 𝒰 𝒾} (x : X) → x ≡ x
_∎ x = refl x
infix  3 _∎

-- b : {A : 𝒰 𝒾} (y z : A) (p q : y ≡ z) → p ≡ q
-- b y z p q = begin
--   p ≡˘⟨ {!!} ⟩
--   (refl y) ∙ p ≡⟨ _ ⟩
--   _
---------------------------------------------------------------------------------

-- Section 2.2 Functions are functors

ap : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} (refl x) = refl (f x)

-- Lemma 2.2.2 i)
ap-refl : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y) (x : X)
        → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

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

∼-naturality : {X : 𝒰 𝒾} {A : 𝒰 𝒿}
               (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
             → H x ∙ ap g p ≡ ap f p ∙ H y
∼-naturality f g H {x} {_} {refl a} = refl-right ∙ refl-left ⁻¹

corollary244 : {X : 𝒰 𝒾} {A : 𝒰 𝒿}
                  (f : A → A) (H : f ∼ id) {x : A}
                → (H (f x)) ≡ (ap f (H x))
corollary244 f H {x} = begin
    H (f x) ≡˘⟨ refl-right ⟩
    H (f x) ∙ (refl (f x)) ≡˘⟨ ap (H (f x) ∙_) (⁻¹-right∙ (H x)) ⟩
    H (f x) ∙ (H x ∙ (H x)⁻¹) ≡˘⟨ ∙-assoc (H (f x)) ⟩
    (H (f x) ∙ H x) ∙ (H x)⁻¹ ≡˘⟨ ap (λ - → (H (f x) ∙ (-)) ∙ (H x)⁻¹) (ap-id (H x)) ⟩
    (H (f x) ∙ (ap id (H x))) ∙ (H x)⁻¹ ≡⟨ ap (_∙ (H x)⁻¹) (∼-naturality f id H) ⟩
    (ap f (H x) ∙ (H x)) ∙ (H x)⁻¹ ≡⟨ ∙-assoc (ap f (H x)) ⟩
    ap f (H x) ∙ ((H x) ∙ (H x)⁻¹) ≡⟨ ap (ap f (H x) ∙_) (⁻¹-right∙ (H x)) ⟩
    ap f (H x) ∙ (refl (f x)) ≡⟨ refl-right ⟩
    ap f (H x) ∎

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
≃-sym : (X : 𝒰 𝒾) (Y : 𝒰 𝒿) → X ≃ Y → Y ≃ X
≃-sym X Y ( f , e ) =
  let ( f⁻¹ , p , q) = ( equivs-are-invs f e )
  in  ( f⁻¹ , invs-are-equivs f⁻¹ (f , q , p) )

-- Lemma 2.4.12 iii)
≃-trans : (A : 𝒰 𝒾) (B : 𝒰 𝒿) (C : 𝒰 𝓀)
        → A ≃ B → B ≃ C → A ≃ C
≃-trans A B C ( f , ef ) ( g , eg ) =
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
  in  ( (g ∘ f) , invs-are-equivs (g ∘ f) ((f⁻¹ ∘ g⁻¹) , h1 , h2) )

---------------------------------------------------------------------------------

-- 2.5 The higher groupoid structure of type formers

---------------------------------------------------------------------------------

-- 2.6 Cartesian product types

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

happly : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} (f g : Π B) → f ≡ g → f ∼ g
happly f g p x = ap (λ - → - x) p

funext : {i j : Level} → 𝒰 ((i ⊔ j)⁺)
funext {i} {j} = {X : 𝒰 i} {A : X → 𝒰 j} (f g : Π A) → is-equiv (happly f g)

---------------------------------------------------------------------------------

-- 2.10 Universes and the univalence axiom

Id→Eq : (X Y : 𝒰 𝒾) → X ≡ Y → X ≃ Y
Id→Eq X X (refl X) = 𝑖𝑑 X , invs-are-equivs (𝑖𝑑 X) (qinv-id-id X)

is-univalent : (i : Level) → 𝒰 (i ⁺)
is-univalent i = (X Y : 𝒰 i) → is-equiv (Id→Eq X Y)

qinv-ua : is-univalent 𝒾 → (X Y : 𝒰 𝒾) → qinv (Id→Eq X Y)
qinv-ua ua X Y = equivs-are-invs (Id→Eq X Y) (ua X Y)

Eq→Id : is-univalent 𝒾 → (X Y : 𝒰 𝒾) → X ≃ Y → X ≡ Y
Eq→Id ua X Y eqv =
  let ((g , f-g) , (h , h-f)) = ua X Y
  in  g eqv

Univalence : 𝓤ω
Univalence = ∀ i → is-univalent i

---------------------------------------------------------------------------------

-- 2.11 Identity type
trHomc- : (A : 𝒰 𝒾) (a x₁ x₂ : A) (p : x₁ ≡ x₂) (q : a ≡ x₁)
          → tr (λ x → a ≡ x) p q ≡ q ∙ p
trHomc- A a x₁ x₂ (refl x₁) (refl x₁) = refl-right ⁻¹

trHom-c : (A : 𝒰 𝒾) (a x₁ x₂ : A) (p : x₁ ≡ x₂) (q : x₁ ≡ a)
          → tr (λ x → x ≡ a) p q ≡ p ⁻¹ ∙ q
trHom-c A a x₁ x₂ (refl x₁) (refl x₁) = refl-right ⁻¹

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
