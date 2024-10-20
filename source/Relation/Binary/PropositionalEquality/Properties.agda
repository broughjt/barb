module Relation.Binary.PropositionalEquality.Properties where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; reflexive; transitive)
open import Function using (identity)

module ≡-Reasoning {a} {A : Set a} where

  open import Relation.Binary.Reasoning.Syntax

  open begin-syntax {A = A} _≡_ identity public
  open ≡-syntax {A = A} _≡_ transitive public
  open end-syntax {A = A} _≡_ reflexive public
