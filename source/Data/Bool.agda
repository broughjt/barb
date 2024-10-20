module Data.Bool where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Level using (Level)

data Bool : Set where
  false true : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

not : Bool → Bool
not true = false
not false = true

_∧_ : Bool → Bool → Bool
true ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true ∨ b = true
false ∨ b = b

if_then_else : {a : Level} {A : Set a} → Bool → A → A → A
if true then t else _ = t
if false then _ else f = f
