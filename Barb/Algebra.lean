import Barb.Syntax

class CommutativeRing (α : Type u) extends Zero α, One α, Add α, Mul α, Neg α where
  add_commutative : ∀ (a b : α), a + b = b + a
  add_associative : ∀ (a b c : α), (a + b) + c = a + (b + c)
  add_identity : ∀ (a : α), a + 0 = a
  add_inverse : ∀ (a : α), a + (-a) = 0

  multiply_commutative : ∀ (a b : α), a * b = b * a
  multiply_associative : ∀ (a b c : α), (a * b) * c = a * (b * c)
  -- TODO: DO we need to make sure 1 \ne 0?
  multiply_identity : ∀ (a : α), a * 1 = a

  left_distributive : ∀ (a b c : α), a * (b + c) = a * b + a * c
  right_distributive : ∀ (a b c : α), (a + b) * c = a * c + b * c
