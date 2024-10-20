module Function.Definitions where

open import Level using (Level)
open import Data.Sigma using (Σ; _×_)
open import Relation.Binary.Core using (HomogenousRelation)

private
  variable
    a ℓ₁ ℓ₂ : Level
    A B : Set a

module _
  (_≈₁_ : HomogenousRelation A ℓ₁) -- Equality over the domain
  (_≈₂_ : HomogenousRelation B ℓ₂) -- Equality over the codomain
  where

  Congruent : (A → B) → Set _
  Congruent f = ∀ {x y} → x ≈₁ y → f x ≈₂ f y

  Injective : (A → B) → Set _
  Injective f = ∀ {x y} → f x ≈₂ f y → x ≈₁ y

  Surjective : (A → B) → Set _
  Surjective f = ∀ y → Σ A (λ x → ∀ {z} → z ≈₁ x → f z ≈₂ y)

  Bijective : (A → B) → Set _
  Bijective f = Injective f × Surjective f

  LeftInverse : (A → B) → (B → A) → Set _
  LeftInverse f g = ∀ {x y} → y ≈₁ g x → f y ≈₂ x

  RightInverse : (A → B) → (B → A) → Set _
  RightInverse f g = ∀ {x y} → y ≈₂ f x → g y ≈₁ x

  Inverse : (A → B) → (B → A) → Set _
  Inverse f g = LeftInverse f g × RightInverse f g
