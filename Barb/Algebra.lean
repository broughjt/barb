import Barb.Syntax

class CommutativeRing (α : Type u) extends Zero α, One α, Add α, Mul α, Neg α where
  add_associative : ∀ (x y z : α), (x + y) + z = x + (y + z)
  add_commutative : ∀ (x y : α), x + y = y + x
  add_identity : ∀ (x : α), x + 0 = x
  add_inverse : ∀ (x : α), x + (-x) = 0

  multiply_associative : ∀ (x y z : α), (x * y) * z = x * (y * z)
  multiply_commutative : ∀ (x y : α), x * y = y * x
  -- TODO: Do we need to make sure 1 \ne 0? Answer, yes, see Nontrivial class in mathlib
  multiply_identity : ∀ (x : α), x * 1 = x

  left_distributive : ∀ (x y z : α), x * (y + z) = x * y + x * z
  right_distributive : ∀ (x y z : α), (x + y) * z = x * z + y * z

class Field (α : Type u) extends CommutativeRing α where
  -- TODO: Pull out into reciprocal operation class which takes a nonzero proof and has nice Inv-like syntax
  reciprocal : (x : α) → x ≠ 0 → α
  multiply_inverse : ∀ (x : α) (h : x ≠ 0), x * (reciprocal x h) = 1
