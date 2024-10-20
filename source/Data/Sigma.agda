module Data.Sigma where

open import Level using (Level; _⊔_)

private
  variable
    a b : Level

record Σ (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    first : A
    second : B first

open Σ public

infixr 4 _,_

{-# BUILTIN SIGMA Σ #-}

infixr 2 _×_

_×_ : ∀ (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ x → B)
