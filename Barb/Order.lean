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

theorem less_equal_of_not_greater_equal [TotalOrder α] {a b : α} : ¬a ≤ b → a ≤ b := 
  Or.resolve_right (less_equal_strongly_connected a b)

theorem less_equal_of_not_less_equal [TotalOrder α] {a b : α} : ¬a ≤ b → b ≤ a := 
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

def minimum_definition [DecidableTotalOrder α] (a b : α) : 
    minimum a b = if a ≤ b then a else b := 
  rfl

def maximum [DecidableTotalOrder α] (a b : α) := if a ≤ b then b else a

def maximum_definition [DecidableTotalOrder α] (a b : α) : 
    maximum a b = if a ≤ b then b else a :=
  rfl

theorem minimum_less_equal_left [DecidableTotalOrder α] (a b : α) : minimum a b ≤ a :=
  if h : a ≤ b
  then by rw [minimum_definition, if_pos h]; exact less_equal_reflexive a
  else by rw [minimum_definition, if_neg h]; exact less_equal_of_not_less_equal h

theorem minimum_less_equal_right [DecidableTotalOrder α] (a b : α) : minimum a b ≤ b :=
  if h : a ≤ b
  then by rw [minimum_definition, if_pos h]; exact h
  else by rw [minimum_definition, if_neg h]; exact less_equal_reflexive b

theorem less_equal_minimum [DecidableTotalOrder α] {a b c : α} (hab : a ≤ b) (hac : a ≤ c) : a ≤ minimum b c :=
  if h : b ≤ c
  then by rw [minimum_definition, if_pos h]; exact hab
  else by rw [minimum_definition, if_neg h]; exact hac

theorem less_equal_maximum_left [DecidableTotalOrder α] (a b : α) : a ≤ maximum a b :=
  if h : a ≤ b
  then by rw [maximum_definition, if_pos h]; exact h
  else by rw [maximum_definition, if_neg h]; exact less_equal_reflexive a

theorem less_equal_maximum_right [DecidableTotalOrder α] (a b : α) : b ≤ maximum a b :=
  if h : a ≤ b
  then by rw [maximum_definition, if_pos h]; exact less_equal_reflexive b
  else by rw [maximum_definition, if_neg h]; exact less_equal_of_not_less_equal h

theorem maximum_less_equal [DecidableTotalOrder α] {a b c : α} (hac : a ≤ c) (hbc : b ≤ c) : maximum a b ≤ c :=
  if h : a ≤ b
  then by rw [maximum_definition, if_pos h]; exact hbc
  else by rw [maximum_definition, if_neg h]; exact hac

theorem equal_minimum [DecidableTotalOrder α] {b c d : α} (hab : b ≤ c) (hac : b ≤ d)
    (hd : ∀ {a}, a ≤ c → a ≤ d → a ≤ b) : b = minimum c d :=
  less_equal_antisymmetric
  (less_equal_minimum hab hac)
  (hd (minimum_less_equal_left c d) (minimum_less_equal_right c d))

theorem minimum_commutative [DecidableTotalOrder α] (a b : α) : minimum a b = minimum b a :=
  equal_minimum 
  (minimum_less_equal_right a b) 
  (minimum_less_equal_left a b)
  (λ hcb hca => less_equal_minimum hca hcb)

theorem minimum_associative [DecidableTotalOrder α] (a b c : α) :
    minimum (minimum a b) c = minimum a (minimum b c) := by
  apply equal_minimum
  . apply less_equal_transitive
    apply minimum_less_equal_left; apply minimum_less_equal_left
  . apply less_equal_minimum
    apply less_equal_transitive; apply minimum_less_equal_left; apply minimum_less_equal_right
    apply minimum_less_equal_right
  . intro d hda hdbc
    apply less_equal_minimum; apply less_equal_minimum hda; apply less_equal_transitive hdbc
    apply minimum_less_equal_left; apply less_equal_transitive hdbc; apply minimum_less_equal_right

@[simp] theorem minimum_self [DecidableTotalOrder α] (a : α) : minimum a a = a := by simp [minimum_definition]

theorem minimum_equal_left [DecidableTotalOrder α] {a b : α} (h : a ≤ b) : minimum a b = a := by
  apply Eq.symm
  apply equal_minimum (less_equal_reflexive a) h
  intro c ha _; exact ha

theorem minimum_equal_right [DecidableTotalOrder α] {a b : α} (h : b ≤ a) : minimum a b = b := by
  apply Eq.symm
  apply equal_minimum h (less_equal_reflexive b)
  intro c _ hb; exact hb

theorem equal_maximum [DecidableTotalOrder α] {a b c : α} (hac : a ≤ c) (hbc : b ≤ c)
    (hd : ∀ {d}, a ≤ d → b ≤ d → c ≤ d) : c = maximum a b :=
  less_equal_antisymmetric
  (hd (less_equal_maximum_left a b) (less_equal_maximum_right a b))
  (maximum_less_equal hac hbc)

theorem maximum_commutative [DecidableTotalOrder α] (a b : α) : maximum a b = maximum b a :=
  equal_maximum
  (less_equal_maximum_right a b)
  (less_equal_maximum_left a b)
  (λ hb ha => maximum_less_equal ha hb)

theorem maximum_associative [DecidableTotalOrder α] (a b c : α) :
    maximum (maximum a b) c = maximum a (maximum b c) := by
    apply equal_maximum
    . apply less_equal_transitive
      apply less_equal_maximum_left a b; apply less_equal_maximum_left
    . apply maximum_less_equal
      apply less_equal_transitive; apply less_equal_maximum_right a b; apply less_equal_maximum_left;
      apply less_equal_maximum_right
    . intro d had hbcd
      apply maximum_less_equal
      apply maximum_less_equal had; apply less_equal_transitive (less_equal_maximum_left _ _) hbcd
      apply less_equal_transitive (less_equal_maximum_right _ _) hbcd

@[simp] theorem maximum_self [DecidableTotalOrder α] (a : α) : maximum a a = a := by simp [maximum_definition]

theorem maximum_equal_left [DecidableTotalOrder α] {a b : α} (h : b ≤ a) : maximum a b = a := by
  apply Eq.symm
  apply equal_maximum (less_equal_reflexive a) h
  intro c ha _; exact ha

theorem maximum_equal_right [DecidableTotalOrder α] {a b : α} (h : a ≤ b) : maximum a b = b := by
  apply Eq.symm
  apply equal_maximum h (less_equal_reflexive b)
  intro c _ hb; exact hb

theorem minimum_equal_left_of_less_than [DecidableTotalOrder α] {a b : α} : a < b → minimum a b = a :=
  minimum_equal_left ∘ less_equal_of_less_than

theorem minimum_equal_right_of_less_than [DecidableTotalOrder α] {a b : α} : b < a → minimum a b = b :=
  minimum_equal_right ∘ less_equal_of_less_than

theorem maximum_equal_left_of_less_than [DecidableTotalOrder α] {a b : α} : b < a → maximum a b = a :=
  maximum_equal_left ∘ less_equal_of_less_than

theorem max_eq_right_of_lt [DecidableTotalOrder α] {a b : α} : a < b → maximum a b = b :=
  maximum_equal_right ∘ less_equal_of_less_than

theorem less_than_minimum [DecidableTotalOrder α] {a b c : α} 
    (hab : a < b) (hac : a < c) : a < minimum b c :=
  Or.elim (less_equal_or_less_than b c)
    (λ h => (minimum_equal_left h).symm ▸ hab)
    (λ h => (minimum_equal_right_of_less_than h).symm ▸ hac)

theorem maximum_less_than [DecidableTotalOrder α] {a b c : α} 
    (hac : a < c) (hbc : b < c) : maximum a b < c :=
  Or.elim (less_equal_or_less_than a b)
    (λ h => (maximum_equal_right h).symm ▸ hbc)
    (λ h => (maximum_equal_left_of_less_than h).symm ▸ hac)

def Monotone [Preorder α] [Preorder β] (f : α → β) := ∀ {a b : α}, a ≤ b → f a ≤ f b

def Antitone [Preorder α] [Preorder β] (f : α → β) := ∀ {a b : α}, a ≤ b → f b ≤ f a

def StrictMonotone [StrictPartialOrder α] [StrictPartialOrder β] (f : α → β) := ∀ {a b : α}, a < b → f a < f b

def StrictAntitone [StrictPartialOrder α] [StrictPartialOrder β] (f : α → β) := ∀ {a b : α}, a < b → f b < f a
