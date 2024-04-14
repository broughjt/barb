import Barb.Logic

class Preorder (α : Type u) extends LE α, LT α where
  less_equal_reflexive : Relation.Reflexive (. ≤ . : α → α → Prop)
  less_equal_transitive : Relation.Transitive (. ≤ . : α → α → Prop)
  lt := λ a b => a ≤ b ∧ ¬b ≤ a
  less_than_equivalent_less_equal_not_less_equal : ∀ {a b : α},
    lt a b ↔ a ≤ b ∧ ¬b ≤ a := by intros; simp

class PartialOrder (α : Type u) extends Preorder α where
  less_equal_antisymmetric : Relation.AntiSymmetric (. ≤ . : α → α → Prop)

class StrictPartialOrder (α : Type u) extends LT α where
  less_than_irreflexive : Relation.Irreflexive (. < . : α → α → Prop)
  less_than_transitive : Relation.Transitive (. < . : α → α → Prop)
  -- Default proof: apply transitivity to a < b and b < a to get a < a, but this is a contradiction since ¬(a < a) for all a : α.
  less_than_asymmetric : Relation.Asymmetric (. < . : α → α → Prop)
    := λ hab hba => less_than_irreflexive _ (less_than_transitive hab hba)

def LessEqual [s : Preorder α] := s.le

def LessThan [s : Preorder α] := s.lt

theorem less_equal_reflexive [Preorder α] : Relation.Reflexive (. ≤ . : α → α → Prop) := Preorder.less_equal_reflexive

theorem less_equal_transitive [Preorder α] : Relation.Transitive (. ≤ . : α → α → Prop) := Preorder.less_equal_transitive

theorem less_than_equivalent_less_equal_not_less_equal [Preorder α] : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.less_than_equivalent_less_equal_not_less_equal

theorem less_equal_antisymmetric [PartialOrder α] : Relation.AntiSymmetric (. ≤ . : α → α → Prop) := PartialOrder.less_equal_antisymmetric

theorem less_than_irreflexive [StrictPartialOrder α] : Relation.Irreflexive (. < . : α → α → Prop) := StrictPartialOrder.less_than_irreflexive

theorem less_than_transitive [StrictPartialOrder α] : Relation.Transitive (. < . : α → α → Prop) := StrictPartialOrder.less_than_transitive

theorem less_than_asymmetric [StrictPartialOrder α] : Relation.Asymmetric (. < . : α → α → Prop) := StrictPartialOrder.less_than_asymmetric

instance strictPartialOrderOfPreorder [Preorder α] : StrictPartialOrder α where
  lt := LessThan
  less_than_irreflexive :=
    λ _ h => 
    let ⟨hl, hr⟩ := less_than_equivalent_less_equal_not_less_equal.mp h
    absurd hl hr
  less_than_transitive :=
    λ hab hbc =>
    let ⟨hab, hba⟩ := less_than_equivalent_less_equal_not_less_equal.mp hab
    let ⟨hbc, _⟩ := less_than_equivalent_less_equal_not_less_equal.mp hbc
    less_than_equivalent_less_equal_not_less_equal.mpr
    (And.intro (less_equal_transitive hab hbc) (λ hca => absurd (less_equal_transitive hbc hca) hba))

theorem less_equal_of_equal [Preorder α] {a b : α} : a = b → a ≤ b := λ h => h ▸ Preorder.less_equal_reflexive a

theorem less_than_of_less_equal_of_not_equal [PartialOrder α] : ∀ {a b : α}, a ≤ b → a ≠ b → a < b
  | _, _, h_less_equal, h_not_equal =>
  less_than_equivalent_less_equal_not_less_equal.mpr (And.intro h_less_equal (mt (less_equal_antisymmetric h_less_equal) h_not_equal))
  
theorem less_equal_of_less_than [Preorder α] : ∀ {a b : α}, a < b → a ≤ b
  | _, _, h => (less_than_equivalent_less_equal_not_less_equal.mp h).left

theorem not_equal_of_less_than [PartialOrder α] {a b : α} (h_less_than : a < b) : a ≠ b :=
  λ h_equal => absurd h_less_than (h_equal ▸ less_than_irreflexive a)
  
theorem less_than_of_less_than_of_less_equal [PartialOrder α] : ∀ {a b c : α}, a < b → b ≤ c → a < c
  | _, _, _, hab, hbc =>
  let ⟨hab, hba⟩ := less_than_equivalent_less_equal_not_less_equal.mp hab
  less_than_equivalent_less_equal_not_less_equal.mpr (And.intro (less_equal_transitive hab hbc) (λ hca => hba (less_equal_transitive hbc hca)))

theorem less_than_of_less_equal_of_less_than [PartialOrder α] : ∀ {a b c : α}, a ≤ b → b < c → a < c
  | _, _, _, hab, hbc =>
  let ⟨hbc, hcb⟩ := less_than_equivalent_less_equal_not_less_equal.mp hbc
  less_than_equivalent_less_equal_not_less_equal.mpr (And.intro (less_equal_transitive hab hbc) (λ hca => hcb (less_equal_transitive hca hab)))

theorem less_equal_of_less_than_or_equal [PartialOrder α] : ∀ {a b : α}, a < b ∨ a = b → a ≤ b
  | _, _, Or.inl h => less_equal_of_less_than h
  | _, _, Or.inr h => less_equal_of_equal h

theorem not_less_equal_of_greater_than [PartialOrder α] {a b : α} (h : a < b) : ¬b ≤ a :=
  (less_than_equivalent_less_equal_not_less_equal.mp h).right

theorem not_less_than_of_greater_equal [PartialOrder α] {a b : α} (h : a ≤ b) : ¬b < a := λ hab => not_less_equal_of_greater_than hab h

theorem less_equal_of_equal_or_less_than [PartialOrder α] : ∀ {a b : α}, a = b ∨ a < b → a ≤ b := less_equal_of_less_than_or_equal ∘ Or.commutative.mp

theorem less_equal_antisymmetric_equivalent_equal [PartialOrder α] : ∀ {a b : α}, a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨λ h_equal => ⟨less_equal_of_equal h_equal, less_equal_of_equal h_equal.symm⟩, λ ⟨hab, hba⟩ => less_equal_antisymmetric hab hba⟩

instance decideEqualOfDecideLessEqual [PartialOrder α] [DecidableRel (. ≤ . : α → α → Prop)] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isTrue (less_equal_antisymmetric hab hba)
      else isFalse λ h_equal => hba (h_equal ▸ less_equal_reflexive a)
    else isFalse λ h_equal => hab (h_equal ▸ less_equal_reflexive a)

instance decideLessThanOfDecideLessEqual [Preorder α] [DecidableRel (. ≤ . : α → α → Prop)] : DecidableRel (. < . : α → α → Prop)
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isFalse λ hba' => (less_than_equivalent_less_equal_not_less_equal.mp hba').right hba
      else isTrue (less_than_equivalent_less_equal_not_less_equal.mpr (And.intro hab hba))
    else isFalse (λ hab' => hab (less_equal_of_less_than hab'))

theorem less_than_or_equal_of_less_equal [PartialOrder α] [DecidableRel (. ≤ . : α → α → Prop)] {a b : α} (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then
    Or.inr (less_equal_antisymmetric hab hba)
  else
    Or.inl (less_than_equivalent_less_equal_not_less_equal.mpr (And.intro hab hba))

theorem equal_or_less_than_of_less_equal [PartialOrder α] [DecidableRel (. ≤ . : α → α → Prop)] :
    ∀ {a b : α}, a ≤ b → a = b ∨ a < b :=
  Or.commutative.mp ∘ less_than_or_equal_of_less_equal

theorem less_equal_equivalent_less_than_or_equal [PartialOrder α] [DecidableRel (. ≤ . : α → α → Prop)] :
    ∀ {a b : α}, a ≤ b ↔ a < b ∨ a = b :=
  ⟨less_than_or_equal_of_less_equal, less_equal_of_less_than_or_equal⟩

class TotalOrder (α : Type u) extends PartialOrder α where
  less_equal_strongly_connected : Relation.StronglyConnected (. ≤ . : α → α → Prop)

class StrictTotalOrder (α : Type u) extends StrictPartialOrder α where
  less_than_connected : Relation.Connected (. < . : α → α → Prop)

class DecidableTotalOrder (α : Type u) extends TotalOrder α where
  decideLessEqual : DecidableRel (. ≤ . : α → α → Prop)
  decideEqual : DecidableEq α := decideEqualOfDecideLessEqual
  decideLessThan : DecidableRel (. < . : α → α → Prop) := decideLessThanOfDecideLessEqual

class DecidableStrictTotalOrder (α : Type u) extends StrictTotalOrder α where
  decideLessThan : DecidableRel (. < . : α → α → Prop)
  decideEqual : DecidableEq α

theorem less_equal_strongly_connected [TotalOrder α] : Relation.StronglyConnected (. ≤ . : α → α → Prop) := TotalOrder.less_equal_strongly_connected

theorem less_than_connected [StrictTotalOrder α] : Relation.Connected (. < . : α → α → Prop) := StrictTotalOrder.less_than_connected

instance [DecidableTotalOrder α] : DecidableRel (. ≤ . : α → α → Prop) := DecidableTotalOrder.decideLessEqual

instance [DecidableStrictTotalOrder α] : DecidableRel (. < . : α → α → Prop) := DecidableStrictTotalOrder.decideLessThan

instance [DecidableStrictTotalOrder α] : DecidableEq α := DecidableStrictTotalOrder.decideEqual

instance strictTotalOrderOfTotalOrder [TotalOrder α] : StrictTotalOrder α where
  less_than_connected :=
    λ h => match less_equal_strongly_connected _ _ with
      | Or.inl hab => Or.inl (less_than_of_less_equal_of_not_equal hab h)
      | Or.inr hba => Or.inr (less_than_of_less_equal_of_not_equal hba h.symm)

theorem less_equal_of_not_greater_equal [TotalOrder α] {a b : α} : 
    ¬a ≥ b → a ≤ b := 
  Or.resolve_right (less_equal_strongly_connected a b)

theorem less_equal_of_not_less_equal [TotalOrder α] {a b : α} : 
    ¬a ≤ b → b ≤ a := 
  Or.resolve_left (less_equal_strongly_connected a b)

theorem less_than_trichotomous [DecidableTotalOrder α] (a b : α) : a < b ∨ a = b ∨ a > b :=
  Or.elim (less_equal_strongly_connected a b)
    (λ h : a ≤ b => Or.elim (less_than_or_equal_of_less_equal h) Or.inl (Or.inr ∘ Or.inl))
    (λ h : a ≥ b => Or.elim (less_than_or_equal_of_less_equal h) (Or.inr ∘ Or.inr) (Or.inr ∘ Or.inl ∘ Eq.symm))

theorem less_equal_of_not_less_than [DecidableTotalOrder α] {a b : α} (h : ¬a < b) : b ≤ a :=
  match less_than_trichotomous b a with
  | Or.inl h_less => less_equal_of_less_than h_less
  | Or.inr (Or.inl h_equal) => less_equal_of_equal h_equal
  | Or.inr (Or.inr h_greater) => absurd h_greater h

theorem less_than_or_less_equal [DecidableTotalOrder α] (a b : α) : a < b ∨ b ≤ a := by
  match less_than_trichotomous a b with
  | Or.inl h_less => exact Or.inl h_less
  | Or.inr (Or.inl h_equal) => exact Or.inr (less_equal_of_equal h_equal.symm)
  | Or.inr (Or.inr h_greater) => exact Or.inr (less_equal_of_less_than h_greater)

theorem less_equal_or_less_than [DecidableTotalOrder α] (a b : α) : a ≤ b ∨ b < a :=
  Or.symmetric (less_than_or_less_equal b a)

def minimum [DecidableTotalOrder α] (a b : α) := if a ≤ b then a else b

def maximum [DecidableTotalOrder α] (a b : α) := if a ≤ b then b else a

def Monotone [Preorder α] [Preorder β] (f : α → β) := ∀ {a b : α}, a ≤ b → f a ≤ f b

def Antitone [Preorder α] [Preorder β] (f : α → β) := ∀ {a b : α}, a ≤ b → f b ≤ f a

def StrictMonotone [StrictPartialOrder α] [StrictPartialOrder β] (f : α → β) := ∀ {a b : α}, a < b → f a < f b

def StrictAntitone [StrictPartialOrder α] [StrictPartialOrder β] (f : α → β) := ∀ {a b : α}, a < b → f b < f a
