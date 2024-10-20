module Data.Option where

data Option {a} (A : Set a) : Set a where
  none : Option A
  some : A → Option A

{-# BUILTIN MAYBE Option #-}
