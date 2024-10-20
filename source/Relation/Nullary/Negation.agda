module Relation.Nullary.Negation where

open import Data.Empty using (⊥; ⊥-eliminate)
open import Function.Core using (_∘_)
open import Level

private
  variable
    a w : Level
    A B : Set a
    W : Set w

infix 3 ¬_
¬_ : Set a → Set a
¬ A = A → ⊥

Stable : Set a → Set a
Stable A = ¬ ¬ A → A

contradiction : A → ¬ A → W
contradiction a ¬a = ⊥-eliminate (¬a a)

contraposition : (A → B) → ¬ B → ¬ A
contraposition f ¬b = ¬b ∘ f
