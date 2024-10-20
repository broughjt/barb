module Data.Empty where

data ⊥ : Set where

⊥-eliminate : ∀ {a} {A : Set a} → ⊥ → A
⊥-eliminate ()
