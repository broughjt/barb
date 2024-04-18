import Barb.Syntax

class CommutativeRing (α : Type u) extends Zero α, One α, Add α, Mul α, Neg α where
  add_associative : ∀ (x y z : α), (x + y) + z = x + (y + z)
  add_commutative : ∀ (x y : α), x + y = y + x
  add_zero : ∀ (x : α), x + 0 = x
  add_inverse : ∀ (x : α), x + (-x) = 0

  multiply_associative : ∀ (x y z : α), (x * y) * z = x * (y * z)
  multiply_commutative : ∀ (x y : α), x * y = y * x
  -- TODO: Do we need to make sure 1 \ne 0? Answer, yes, see Nontrivial class in mathlib
  multiply_one : ∀ (x : α), x * 1 = x

  left_distributive : ∀ (x y z : α), x * (y + z) = x * y + x * z
  right_distributive : ∀ (x y z : α), (x + y) * z = x * z + y * z

class Nontrivial (α : Type u) : Prop where
  exists_pair_not_equal : ∃ x y : α, x ≠ y

def NonZero (α : Type u) [Zero α] := { a : α // a ≠ 0 }

class Field (α : Type u) extends CommutativeRing α, Nontrivial α, Invert (NonZero α) where
  multiply_inverse : ∀ x : NonZero α, x.val * (invert x).val = 1
