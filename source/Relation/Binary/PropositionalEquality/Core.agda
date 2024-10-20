module Relation.Binary.PropositionalEquality.Core where

open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.Core
open import Relation.Nullary.Negation using (¬_)

private
  variable
    a : Level
    A B : Set a

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  reflexive : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≢_
_≢_ : {A : Set a} → HomogenousRelation A a
x ≢ y = ¬ x ≡ y

reflexive' : Reflexive {A = A} _≡_
reflexive' = reflexive

symmetric : HomogenousSymmetric {A = A} _≡_
symmetric reflexive = reflexive

-- TODO: Understand why naming first argument reflexive works
transitive : HomogeneousTransitive {A = A} _≡_
transitive reflexive hyz = hyz

-- substitutive : Substitutive {A = A} _≡_ ℓ
-- substitutive P reflexive p = p

≢-symmetric : HomogenousSymmetric {A = A} _≢_
≢-symmetric hxy = hxy ∘ symmetric

congruent : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
congruent f reflexive = reflexive
