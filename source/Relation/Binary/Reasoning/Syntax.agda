module Relation.Binary.Reasoning.Syntax where

open import Level
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

private
  variable
    a ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B C : Set a
    x y z : A

module begin-syntax
  (R : Relation A B ℓ₁)
  {S : Relation A B ℓ₂}
  (relator : R ⇒ S)
  where

  infix 1 begin_

  begin_ : R x y → S x y
  begin_ = relator

module _
  {R : Relation A B ℓ₁}
  (S : Relation B C ℓ₂)
  (T : Relation A C ℓ₃)
  (step : Transitive R S T)
  where

  forward : ∀ (x : A) {y z} → S y z → R x y → T x z
  forward x ySz xRy = step {x} xRy ySz

  module _
    {U : Relation B A ℓ₄}
    (symmetric : Symmetric U R)
    where

    backward : ∀ x {y z} → S y z → U y x → T x z
    backward x ySz yUx = step (symmetric yUx) ySz

module ≡-syntax
  (R : Relation A B ℓ₁)
  (step : Transitive _≡_ R R)
  where

  infixr 2 step-≡-⟩  step-≡-∣ step-≡-⟨
  step-≡-⟩ = forward R R step

  step-≡-∣ : ∀ x {y} → R x y → R x y
  step-≡-∣ x xRy = xRy

  step-≡-⟨ = backward R R step ≡.symmetric

  syntax step-≡-⟩ x yRz x≡y = x ≡⟨ x≡y ⟩ yRz
  syntax step-≡-∣ x xRy     = x ≡⟨⟩ xRy
  syntax step-≡-⟨ x yRz y≡x = x ≡⟨ y≡x ⟨ yRz

module end-syntax
  (R : HomogenousRelation A ℓ₁)
  (reflexive : Reflexive R)
  where

  infix 3 _∎

  _∎ : ∀ x → R x x
  x ∎ = reflexive
