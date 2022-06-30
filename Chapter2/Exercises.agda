module Chapter2.Exercises where

open import Chapter2.Book public

-- Exercise 2.10
Σ-assoc : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {C : (Σ x ꞉ A , B x) → 𝒰 𝓀}
        → (Σ x ꞉ A , (Σ y ꞉ B x , C (x , y))) ≃ (Σ p ꞉ (Σ x ꞉ A , B x) , C p)
Σ-assoc = map , invs-are-equivs map (map⁻¹ , ε , η)
 where
  map = λ (x , y , c) → ((x , y) , c)
  map⁻¹ = λ ((x , y) , c) → (x , y , c)
  ε = λ - → refl -
  η = λ - → refl -
