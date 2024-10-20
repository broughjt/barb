open import Relation.Binary using (HomogenousRelation)

module Algebra
  {a ℓ} {A : Set a}
  (_≈_ : HomogenousRelation A ℓ)
  where

  open import Data.Sigma using (_×_)

  Operator₁ : ∀ {ℓ} → Set ℓ → Set ℓ
  Operator₁ A = A → A
  
  Operator₂ : ∀ {ℓ} → Set ℓ → Set ℓ
  Operator₂ A = A → A → A

  Associative : Operator₂ A → Set _
  Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

  Commutative : Operator₂ A → Set _
  Commutative _∙_ = ∀ x y → (x ∙ y) ≈ (y ∙ x)

  LeftIdentity : A → Operator₂ A → Set _
  LeftIdentity e _∙_ = ∀ x → (e ∙ x) ≈ x

  RightIdentity : A → Operator₂ A → Set _
  RightIdentity e _∙_ = ∀ x → (x ∙ e) ≈ x

  Identity : A → Operator₂ A → Set _
  Identity e _∙_ = (LeftIdentity e _∙_) × (RightIdentity e _∙_)

  LeftZero : A → Operator₂ A → Set _
  LeftZero z _∙_ = ∀ x → (z ∙ x) ≈ z
  
  RightZero : A → Operator₂ A → Set _
  RightZero z _∙_ = ∀ x → (x ∙ z) ≈ z
  
  Zero : A → Operator₂ A → Set _
  Zero z ∙ = (LeftZero z ∙) × (RightZero z ∙)

  infix 4 _LeftDistributesOver_ _RightDistributesOver_ _DistributesOver_

  _LeftDistributesOver_ : Operator₂ A → Operator₂ A → Set _
  _*_ LeftDistributesOver _+_ =
    ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))
  
  _RightDistributesOver_ : Operator₂ A → Operator₂ A → Set _
  _*_ RightDistributesOver _+_ =
    ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))
  
  _DistributesOver_ : Operator₂ A → Operator₂ A → Set _
  * DistributesOver + = (* LeftDistributesOver +) × (* RightDistributesOver +)

  infix 4 _IdempotentOn_

  _IdempotentOn_ : Operator₂ A → A → Set _
  _∙_ IdempotentOn x = (x ∙ x) ≈ x

  Idempotent : Operator₂ A → Set _
  Idempotent _∙_ = ∀ {x} → _∙_ IdempotentOn x
  
  Involutive : Operator₁ A → Set _
  Involutive f = ∀ x → f (f x) ≈ x
  
  LeftCancellative : Operator₂ A → Set _
  LeftCancellative _•_ = ∀ x y z → (x • y) ≈ (x • z) → y ≈ z
  
  RightCancellative : Operator₂ A → Set _
  RightCancellative _•_ = ∀ x y z → (y • x) ≈ (z • x) → y ≈ z
  
  Cancellative : Operator₂ A → Set _
  Cancellative _•_ = (LeftCancellative _•_) × (RightCancellative _•_)
