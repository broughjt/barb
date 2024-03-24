import Barb.Logic

universe u
variable {α : Type u}

section Preorder

-- Copying a bit of this from mathlib to get a sense of what's even possible. Also reading the wikipedia article on pre and partial orders. The basic idea is that each preorder induces a strict partial order, and this will get rid of a bunch of theorems I proved about natural numbers and was about to prove again for integers

class Preorder (α : Type u) extends LE α where
  less_equal_reflexive : Relation.Reflexive (. ≤ . : α → α → Prop)
  less_equal_transitive : Relation.Transitive (. ≤ . : α → α → Prop)
  less_than := λ x y : α => (x ≤ y ∧ ¬y ≤ x)
  less_than_equivalent_less_equal_not_less_equal : ∀ x y : α, less_than x y ↔ x ≤ y ∧ ¬y ≤ x := by intro; simp
  
instance [Preorder α] : LT α where
  lt := Preorder.less_than
  
variable [Preorder α]

@[simp] theorem less_equal_reflexive : Relation.Reflexive (. ≤ . : α → α → Prop) := Preorder.less_equal_reflexive

theorem less_equal_transitive : Relation.Transitive (. ≤ . : α → α → Prop) := Preorder.less_equal_transitive

theorem less_than_equivalent_less_equal_not_less_equal : ∀ {x y : α}, x < y ↔ x ≤ y ∧ ¬y ≤ x :=
  Preorder.less_than_equivalent_less_equal_not_less_equal _ _
  
theorem less_than_of_less_equal_not_less_equal : ∀ {x y : α}, x ≤ y → ¬y ≤ x → x < y
  | x, y, hab, hba => (Preorder.less_than_equivalent_less_equal_not_less_equal x y).mpr ⟨hab, hba⟩
  
theorem less_equal_not_less_equal_of_less_than : ∀ {x y : α}, x < y → x ≤ y ∧ ¬y ≤ x
  | x, y, h => (Preorder.less_than_equivalent_less_equal_not_less_equal x y).mp h

theorem less_equal_of_equal {x y : α} : x = y → x ≤ y := λ h => h ▸ Preorder.less_equal_reflexive x

@[simp] theorem less_than_irreflexive : Relation.Irreflexive (. < . : α → α → Prop)
  | x, h =>
  have : x ≤ x ∧ ¬(x ≤ x) := less_equal_not_less_equal_of_less_than h
  absurd this.left this.right
  
theorem less_than_transitive : Relation.Transitive (. < . : α → α → Prop)
  | _x, _y, _z, hxy, hyz =>
  let ⟨hxy, _hyx⟩ := less_equal_not_less_equal_of_less_than hxy
  let ⟨hyz, hzy⟩ := less_equal_not_less_equal_of_less_than hyz
  less_than_of_less_equal_not_less_equal (less_equal_transitive hxy hyz) (λ hzx => hzy (less_equal_transitive hzx hxy))

theorem not_equal_of_less_than {x y : α} (h_less_than : x < y) : x ≠ y := 
  λ h_equal => absurd h_less_than (h_equal ▸ less_than_irreflexive x)
  
theorem less_than_asymmetric : Relation.Asymmetric (. < . : α → α → Prop)
  | x, _y, hxy, hyx =>
  less_than_irreflexive x (less_than_transitive hxy hyx)
  
theorem less_equal_of_less_than : ∀ {x y : α}, x < y → x ≤ y
  | _x, _y, h => (less_equal_not_less_equal_of_less_than h).left

theorem less_than_of_less_than_of_less_equal : ∀ {x y z : α}, x < y → y ≤ z → x < z
  | _, _, _, hxy, hyz =>
  let ⟨hxy, hyx⟩ := less_equal_not_less_equal_of_less_than hxy
  less_than_of_less_equal_not_less_equal (less_equal_transitive hxy hyz) (λ hzx => hyx (less_equal_transitive hyz hzx))
  
theorem less_than_of_less_equal_of_less_than : ∀ {x y z : α}, x ≤ y → y < z → x < z
  | _, _, _, hxy, hyz =>
  let ⟨hyz, hzy⟩ := less_equal_not_less_equal_of_less_than hyz
  less_than_of_less_equal_not_less_equal (less_equal_transitive hxy hyz) (λ hzx => hzy (less_equal_transitive hzx hxy))

theorem less_equal_of_less_than_or_equal : ∀ {x y : α}, x < y ∨ x = y → x ≤ y
  | _, _, Or.inl h => less_equal_of_less_than h
  | _, _, Or.inr h => less_equal_of_equal h

theorem not_less_equal_of_greater_than {x y : α} (h : x > y) : ¬x ≤ y :=
  (less_equal_not_less_equal_of_less_than h).right
  
theorem not_less_than_of_greater_equal {x y : α} (h : x ≥ y) : ¬x < y := λ hxy => not_less_equal_of_greater_than hxy h
  
theorem less_equal_of_equal_or_less_than : ∀ {x y : α}, x = y ∨ x < y → x ≤ y := less_equal_of_less_than_or_equal ∘ Or.commutative.mp

instance decidableLessThanOfDecidableLessEqual [@DecidableRel α (. ≤ .)] : @DecidableRel α (. < .)
  | x, y =>
    if hxy : x ≤ y then 
      if hyx : y ≤ x then isFalse λ hyx' => (less_equal_not_less_equal_of_less_than hyx').right hyx
      else isTrue (less_than_of_less_equal_not_less_equal hxy hyx)
    else isFalse (λ hxy' => hxy (less_equal_of_less_than hxy'))

end Preorder

section PartialOrder

class PartialOrder (α : Type u) extends Preorder α where
  less_equal_antisymmetric : Relation.AntiSymmetric le

variable [PartialOrder α]

theorem less_equal_antisymmetric : Relation.AntiSymmetric (. ≤ . : α → α → Prop) :=
  PartialOrder.less_equal_antisymmetric
  
theorem less_equal_antisymmetric_equivalent_equal : ∀ {x y : α}, x = y ↔ x ≤ y ∧ y ≤ x :=
  ⟨λ h_equal => ⟨less_equal_of_equal h_equal, less_equal_of_equal h_equal.symm⟩, λ ⟨hxy, hyx⟩ => less_equal_antisymmetric hxy hyx⟩

theorem less_than_of_less_equal_of_not_equal : ∀ {x y : α}, x ≤ y → x ≠ y → x < y
  | _, _, h_less_equal, h_not_equal =>
  less_than_of_less_equal_not_less_equal h_less_equal (mt (less_equal_antisymmetric h_less_equal) h_not_equal)
  
instance decidableEqualOfDecidableLessEqual [@DecidableRel α (. ≤ .)] : DecidableEq α
  | x, y =>
    if hxy : x ≤ y then
      if hyx : y ≤ x then isTrue (less_equal_antisymmetric hxy hyx) 
      else isFalse λ h_equal => hyx (h_equal ▸ less_equal_reflexive x)
    else isFalse λ h_equal => hxy (h_equal ▸ less_equal_reflexive x)
    
namespace Decidable

variable [@DecidableRel α (· ≤ ·)]

theorem less_than_or_equal_of_less_equal {x y : α} (hxy : x ≤ y) : x < y ∨ x = y :=
  if hyx : y ≤ x then 
    Or.inr (less_equal_antisymmetric hxy hyx) 
  else 
    Or.inl (less_than_of_less_equal_not_less_equal hxy hyx)

theorem equal_or_less_than_of_less_equal : ∀ {x y : α}, x ≤ y → x = y ∨ x < y := Or.commutative.mp ∘ less_than_or_equal_of_less_equal

theorem less_equal_equivalent_less_than_or_equal : ∀ {x y : α}, x ≤ y ↔ x < y ∨ x = y := 
  ⟨less_than_or_equal_of_less_equal, less_equal_of_less_than_or_equal⟩

end Decidable

end PartialOrder

section TotalOrder

-- Are all total orders necessarilly decidable? Does the strongly connected property imply this?
class TotalOrder (α : Type u) extends PartialOrder α where
  less_equal_strongly_connected : Relation.StronglyConnected le
  decidableLessEqual : DecidableRel (. ≤ . : α → α → Prop)
  decidableEqual : DecidableEq α := @decidableEqualOfDecidableLessEqual _ _ decidableLessEqual
  decidableLessThan : DecidableRel (. < . : α → α → Prop) := @decidableLessThanOfDecidableLessEqual _ _ decidableLessEqual
  minimum (x y : α) := if x ≤ y then x else y
  maximum (x y : α) := if x ≤ y then y else x
  minimum_definition : ∀ x y, minimum x y = if x ≤ y then x else y := by simp
  maximum_definition : ∀ x y, maximum x y = if x ≤ y then y else x := by simp
  compare (x y : α) := compareOfLessAndEq x y
  compare_equal_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by simp
  
variable [TotalOrder α]

-- TODO: What does this mean?
attribute [local instance] TotalOrder.decidableLessEqual

theorem less_equal_strongly_connected : Relation.StronglyConnected (. ≤ . : α → α → Prop) := TotalOrder.less_equal_strongly_connected

theorem less_equal_of_not_greater_equal {x y : α} : ¬x ≥ y → x ≤ y := Or.resolve_right (less_equal_strongly_connected x y)

theorem less_equal_of_not_less_equal {x y : α} : ¬x ≤ y → y ≤ x := Or.resolve_left (less_equal_strongly_connected x y)

theorem less_than_trichotomous (x y : α) : x < y ∨ x = y ∨ x > y :=
  Or.elim (less_equal_strongly_connected x y)
    (λ h : x ≤ y => Or.elim (Decidable.less_than_or_equal_of_less_equal h) Or.inl (Or.inr ∘ Or.inl))
    (λ h : x ≥ y => Or.elim (Decidable.less_than_or_equal_of_less_equal h) (Or.inr ∘ Or.inr) (Or.inr ∘ Or.inl ∘ Eq.symm))

theorem less_equal_of_not_less_than {x y : α} (h : ¬y < x) : x ≤ y :=
  match less_than_trichotomous x y with
  | Or.inl h_less => less_equal_of_less_than h_less
  | Or.inr (Or.inl h_equal) => less_equal_of_equal h_equal
  | Or.inr (Or.inr h_greater) => absurd h_greater h

theorem less_than_or_less_equal (x y : α) : x < y ∨ y ≤ x := by
  match less_than_trichotomous x y with
  | Or.inl h_less => exact Or.inl h_less
  | Or.inr (Or.inl h_equal) => exact Or.inr (less_equal_of_equal h_equal.symm)
  | Or.inr (Or.inr h_greater) => exact Or.inr (less_equal_of_less_than h_greater)

theorem less_equal_or_less_than (x y : α) : x ≤ y ∨ y < x :=
  Or.symmetric (less_than_or_less_equal y x)
  
end TotalOrder
