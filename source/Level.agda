module Level where

-- Literally just so we don't have to type Agda.Primitive so many times

open import Agda.Primitive public
  using (Level; _⊔_; Setω)
  renaming (lzero to zero; lsuc to successor)
