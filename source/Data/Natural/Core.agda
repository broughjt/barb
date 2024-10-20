module Data.Natural.Core where

data ℕ : Set where
  zero : ℕ
  successor : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + m = m
successor n + m = successor (n + m)
