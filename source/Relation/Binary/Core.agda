module Relation.Binary.Core where

open import Level
open import Function.Core using (flip)
open import Relation.Nullary.Negation using (¬_)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

Relation : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ successor ℓ)
Relation A B ℓ = A → B → Set ℓ

HomogenousRelation : Set a → (ℓ : Level) → Set (a ⊔ successor ℓ)
HomogenousRelation A ℓ = Relation A A ℓ

_⇒_ : Relation A B ℓ₁ → Relation A B ℓ₂ → Set _
P ⇒ Q = ∀ {x y} → P x y → Q x y

Reflexive : HomogenousRelation A ℓ → Set _
Reflexive _∼_ = ∀ {x} → x ∼ x

Symmetric : Relation A B ℓ₁ → Relation B A ℓ₂ → Set _
Symmetric P Q = P ⇒ flip Q

HomogenousSymmetric : HomogenousRelation A ℓ₁ → Set _
HomogenousSymmetric _∼_ = Symmetric _∼_ _∼_

Transitive : Relation A B ℓ₁ → Relation B C ℓ₂ → Relation A C ℓ₃ → Set _
Transitive P Q R = ∀ {x y z } → P x y → Q y z → R x z

HomogeneousTransitive : HomogenousRelation A ℓ → Set _
HomogeneousTransitive _∼_ = Transitive _∼_ _∼_ _∼_

Antisymmetric : Relation A B ℓ₁ → Relation A B ℓ₂ → Relation B A ℓ₃ → Set _
Antisymmetric _≈_ R S = ∀ {x y} → R x y → S y x → x ≈ y

HomogenousAntisymmetric : HomogenousRelation A ℓ₁ → HomogenousRelation A ℓ₂ → Set _
HomogenousAntisymmetric _≈_ _≤_ = Antisymmetric _≈_ _≤_ _≤_

Irreflexive : Relation A B ℓ₁ → Relation A B ℓ₂ → Set _
Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → ¬(x < y)

Asymmetric : Relation A B ℓ₁ → Relation B A ℓ₂ → Set _
Asymmetric R S = ∀ {x y} → R x y → ¬(S y x)

HomogeneousAsymmetric : HomogenousRelation A ℓ → Set _
HomogeneousAsymmetric _<_ = Asymmetric _<_ _<_

_⟶_Respects_ : (A → Set ℓ₁) → (B → Set ℓ₂) → Relation A B ℓ₃ → Set _
P ⟶ Q Respects _∼_ = ∀ {x y} → x ∼ y → P x → Q y

_Respects_ : (A → Set ℓ₁) → HomogenousRelation A ℓ₂ → Set _
P Respects _∼_ = P ⟶ P Respects _∼_

Substitutive : HomogenousRelation A ℓ₁ → (ℓ₂ : Level) → Set _
Substitutive {A = A} _∼_ p = (P : A → Set p) → P Respects _∼_
