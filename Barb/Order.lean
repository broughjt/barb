import Barb.Function
import Barb.Logic
import Barb.Relation
import Barb.Syntax

class Preorder (α : Type u) extends LE α, LT α where
  less_equal_reflexive : Reflexive (. ≤ . : α → α → Prop)
  less_equal_transitive : Transitive (. ≤ . : α → α → Prop)
  lt := λ a b => a ≤ b ∧ ¬b ≤ a
  less_than_equivalent_less_equal_not_less_equal : ∀ {a b : α},
    lt a b ↔ a ≤ b ∧ ¬b ≤ a := by intros; simp

class PartialOrder (α : Type u) extends Preorder α where
  less_equal_antisymmetric : AntiSymmetric (. ≤ . : α → α → Prop)

class StrictPartialOrder (α : Type u) extends LT α where
  less_than_irreflexive : Irreflexive (. < . : α → α → Prop)
  less_than_transitive : Transitive (. < . : α → α → Prop)
  -- Default proof: apply transitivity to a < b and b < a to get a < a, but this is a contradiction since ¬(a < a) for all a : α.
  less_than_asymmetric : Asymmetric (. < . : α → α → Prop)
    := λ hab hba => less_than_irreflexive _ (less_than_transitive hab hba)

def LessEqual [s : Preorder α] := s.le

def LessThan [s : Preorder α] := s.lt

theorem less_equal_reflexive [Preorder α] : Reflexive (. ≤ . : α → α → Prop) := Preorder.less_equal_reflexive

theorem less_equal_transitive [Preorder α] : Transitive (. ≤ . : α → α → Prop) := Preorder.less_equal_transitive

theorem less_than_equivalent_less_equal_not_less_equal [Preorder α] : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.less_than_equivalent_less_equal_not_less_equal

theorem less_equal_antisymmetric [PartialOrder α] : AntiSymmetric (. ≤ . : α → α → Prop) := PartialOrder.less_equal_antisymmetric

theorem less_than_irreflexive [StrictPartialOrder α] : Irreflexive (. < . : α → α → Prop) := StrictPartialOrder.less_than_irreflexive

theorem less_than_transitive [StrictPartialOrder α] : Transitive (. < . : α → α → Prop) := StrictPartialOrder.less_than_transitive

theorem less_than_asymmetric [StrictPartialOrder α] : Asymmetric (. < . : α → α → Prop) := StrictPartialOrder.less_than_asymmetric

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
  less_equal_strongly_connected : StronglyConnected (. ≤ . : α → α → Prop)

class StrictTotalOrder (α : Type u) extends StrictPartialOrder α where
  less_than_connected : Connected (. < . : α → α → Prop)

class DecidableTotalOrder (α : Type u) extends TotalOrder α where
  decideLessEqual : DecidableRel (. ≤ . : α → α → Prop)
  decideEqual : DecidableEq α := decideEqualOfDecideLessEqual
  decideLessThan : DecidableRel (. < . : α → α → Prop) := decideLessThanOfDecideLessEqual

class DecidableStrictTotalOrder (α : Type u) extends StrictTotalOrder α where
  decideLessThan : DecidableRel (. < . : α → α → Prop)
  decideEqual : DecidableEq α

theorem less_equal_strongly_connected [TotalOrder α] : StronglyConnected (. ≤ . : α → α → Prop) := TotalOrder.less_equal_strongly_connected

theorem less_than_connected [StrictTotalOrder α] : Connected (. < . : α → α → Prop) := StrictTotalOrder.less_than_connected

instance [DecidableTotalOrder α] : DecidableRel (. ≤ . : α → α → Prop) := DecidableTotalOrder.decideLessEqual

instance [DecidableStrictTotalOrder α] : DecidableRel (. < . : α → α → Prop) := DecidableStrictTotalOrder.decideLessThan

instance [DecidableStrictTotalOrder α] : DecidableEq α := DecidableStrictTotalOrder.decideEqual

instance strictTotalOrderOfTotalOrder [TotalOrder α] : StrictTotalOrder α where
  less_than_connected :=
    λ h => match less_equal_strongly_connected _ _ with
      | Or.inl hab => Or.inl (less_than_of_less_equal_of_not_equal hab h)
      | Or.inr hba => Or.inr (less_than_of_less_equal_of_not_equal hba h.symm)

theorem less_equal_of_not_greater_equal [TotalOrder α] {a b : α} : ¬b ≤ a → a ≤ b := 
  Or.resolve_right (less_equal_strongly_connected a b)

theorem greater_equal_of_not_less_equal [TotalOrder α] {a b : α} : ¬a ≤ b → b ≤ a := 
  Or.resolve_left (less_equal_strongly_connected a b)

theorem less_than_trichotomous [DecidableTotalOrder α] (a b : α) : a < b ∨ a = b ∨ a > b :=
  Or.elim (less_equal_strongly_connected a b)
    (λ h : a ≤ b => Or.elim (less_than_or_equal_of_less_equal h) Or.inl (Or.inr ∘ Or.inl))
    (λ h : a ≥ b => Or.elim (less_than_or_equal_of_less_equal h) (Or.inr ∘ Or.inr) (Or.inr ∘ Or.inl ∘ Eq.symm))

theorem less_equal_of_not_greater_than [DecidableTotalOrder α] {a b : α} (h : ¬a < b) : b ≤ a :=
  match less_than_trichotomous b a with
  | Or.inl h_less => less_equal_of_less_than h_less
  | Or.inr (Or.inl h_equal) => less_equal_of_equal h_equal
  | Or.inr (Or.inr h_greater) => absurd h_greater h

theorem less_than_of_not_greater_equal [DecidableTotalOrder α] {a b : α} (h : ¬a ≤ b) : b < a :=
  match less_than_trichotomous b a with
  | Or.inl h_less => h_less
  | Or.inr (Or.inl h_equal) => False.elim <| h <| less_equal_of_equal h_equal.symm
  | Or.inr (Or.inr h_greater) => False.elim <| h <| less_equal_of_less_than h_greater

theorem less_than_or_less_equal [DecidableTotalOrder α] (a b : α) : a < b ∨ b ≤ a := by
  match less_than_trichotomous a b with
  | Or.inl h_less => exact Or.inl h_less
  | Or.inr (Or.inl h_equal) => exact Or.inr (less_equal_of_equal h_equal.symm)
  | Or.inr (Or.inr h_greater) => exact Or.inr (less_equal_of_less_than h_greater)

theorem less_equal_or_less_than [DecidableTotalOrder α] (a b : α) : a ≤ b ∨ b < a :=
  Or.symmetric (less_than_or_less_equal b a)

theorem equal_of_forall_less_equal_equivalent [PartialOrder α] {a b : α} (h : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
  less_equal_antisymmetric
    ((h b).mpr <| less_equal_reflexive b)
    ((h a).mp <| less_equal_reflexive a)

def OrderDual (α : Type u) : Type u := α

notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

instance (α : Type u) [LE α] : LE αᵒᵈ where
  le (a b : α) := b ≤ a

instance (α : Type u) [LT α] : LT αᵒᵈ where
  lt (a b : α) := b < a

instance instancePreorder (α : Type u) [Preorder α] : Preorder αᵒᵈ where
  less_equal_reflexive := λ _ => @less_equal_reflexive α _ _
  less_equal_transitive := λ hab hbc => @less_equal_transitive α _ _ _ _ hbc hab
  less_than_equivalent_less_equal_not_less_equal := less_than_equivalent_less_equal_not_less_equal

instance instancePartialOrder (α : Type u) [PartialOrder α] : PartialOrder αᵒᵈ where
  less_equal_antisymmetric := λ hab hba => @less_equal_antisymmetric α _ _ _ hba hab 

instance instanceTotalOrder (α : Type u) [TotalOrder α] : TotalOrder αᵒᵈ where
  less_equal_strongly_connected := λ _ _ => @less_equal_strongly_connected α _ _ _

instance instanceDecidableTotalOrder (α : Type u) [DecidableTotalOrder α] : DecidableTotalOrder αᵒᵈ where
  decideLessEqual a b := @DecidableTotalOrder.decideLessEqual α _ b a

end OrderDual

structure Join [Preorder α] (a b j : α) : Prop where
  less_equal_join_left : a ≤ j
  less_equal_join_right : b ≤ j
  join_least_upper_bound : ∀ {c : α}, a ≤ c → b ≤ c → j ≤ c

class SemilatticeJoin (α : Type u) extends Supremum α, PartialOrder α where
  join : ∀ a b : α, Join a b (a ⊔ b)

theorem less_equal_join_left [SemilatticeJoin α] (a b : α) : a ≤ a ⊔ b :=
  (SemilatticeJoin.join a b).less_equal_join_left

theorem less_equal_join_right [SemilatticeJoin α] (a b : α) : b ≤ a ⊔ b :=
  (SemilatticeJoin.join a b).less_equal_join_right

theorem join_least_upper_bound [SemilatticeJoin α] {a b c : α} : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
  (SemilatticeJoin.join a b).join_least_upper_bound

theorem less_equal_join_of_less_equal_left [SemilatticeJoin α] {a b : α} (c : α) (h : a ≤ b) : a ≤ b ⊔ c :=
  less_equal_transitive h (less_equal_join_left b c)

theorem less_equal_join_of_less_equal_right [SemilatticeJoin α] {a b : α} (c : α) (h : c ≤ b) : c ≤ a ⊔ b :=
  less_equal_transitive h (less_equal_join_right a b)

theorem join_less_equal_equivalent [SemilatticeJoin α] {a b c : α} : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  constructor
  . intro h
    constructor
    . exact less_equal_transitive (less_equal_join_left a b) h
    . exact less_equal_transitive (less_equal_join_right a b) h
  . intro ⟨hac, hbc⟩; exact join_least_upper_bound hac hbc

theorem join_equal_left [SemilatticeJoin α] {a b : α} : a ⊔ b = a ↔ b ≤ a := by
  apply less_equal_antisymmetric_equivalent_equal.trans
  simp [join_less_equal_equivalent, less_equal_reflexive a, less_equal_join_left]

theorem join_equal_right [SemilatticeJoin α] {a b : α} : a ⊔ b = b ↔ a ≤ b := by
  apply less_equal_antisymmetric_equivalent_equal.trans
  simp [join_less_equal_equivalent, less_equal_reflexive b, less_equal_join_right]

theorem join_idempotent [SemilatticeJoin α] {a : α} : a ⊔ a = a := by
  exact join_equal_left.mpr (less_equal_reflexive a)

theorem join_commutative [SemilatticeJoin α] {a b : α} : a ⊔ b = b ⊔ a := by
  apply less_equal_antisymmetric
  . exact join_less_equal_equivalent.mpr ⟨less_equal_join_right b a, less_equal_join_left b a⟩
  . exact join_less_equal_equivalent.mpr ⟨less_equal_join_right a b, less_equal_join_left a b⟩

theorem join_associative [SemilatticeJoin α] {a b c : α} : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) := by
  apply equal_of_forall_less_equal_equivalent
  intro d
  simp [join_less_equal_equivalent, And.associative]

theorem join_unique [PartialOrder α] {a b j k : α} : Join a b j → Join a b k → j = k := by
  intro ⟨haj, hbj, hj⟩ ⟨hak, hbk, hk⟩
  have hjk := hj hak hbk
  have hkj := hk haj hbj
  exact less_equal_antisymmetric hjk hkj

-- Don't have the patience right now
-- Type classes in a functional programming language are seriously a joke, aren't you guys supposed to be the ones
-- that understand that global mutable state is bad?
/-
instance fromAlgebraic {α : Type u} [Supremum α]
    {join_commutative : ∀ a b : α, a ⊔ b = b ⊔ a}
    {join_associative : ∀ a b c : α, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)}
    {join_idempotent : ∀ a : α, a ⊔ a = a}
    : PartialOrder α where
  le a b := a ⊔ b = b
  less_equal_reflexive := join_idempotent
  less_equal_antisymmetric := by
    intro a b hab hba
    rw [← hba]; rw (config := {occs := .pos [2]}) [← hab]
    rw [join_commutative]
  less_equal_transitive := by
    unfold Transitive
    intro a b c hab hbc
    simp at hab; simp at hbc; simp
    rw [← hbc]; rw (config := {occs := .pos [2]}) [← hab]
    rw [join_associative]

def SemilatticeJoin.from_algebraic {α : Type u} [Supremum α]
    (join_commutative : ∀ a b : α, a ⊔ b = b ⊔ a)
    (join_associative : ∀ a b c : α, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (join_idempotent : ∀ a : α, a ⊔ a = a) :
    SemilatticeJoin α where
  join a b :=
    let less_equal_join_left := by 
      sorry
    let less_equal_join_right := by sorry
      -- intro a b
      -- simp
      -- rw [join_commutative, join_associative, join_idempotent]
    let join_least_upper_bound := by sorry
      -- let intro a b c hac hbc
      -- let simp at hac; simp at hbc; simp
      -- let rw [join_associative, hbc]
      -- let exact hac
    @Join.mk sorry 
      less_equal_join_left less_equal_join_right join_least_upper_bound
-/

structure Meet [Preorder α] (a b m : α) where
  meet_less_equal_left : m ≤ a
  meet_less_equal_right : m ≤ b
  meet_greatest_lower_bound : ∀ {c : α}, c ≤ a → c ≤ b → c ≤ m

class SemilatticeMeet (α : Type u) extends Infimum α, PartialOrder α where
  meet : ∀ a b : α, Meet a b (a ⊓ b)

theorem meet_less_equal_left [SemilatticeMeet α] (a b : α) : a ⊓ b ≤ a :=
  (SemilatticeMeet.meet a b).meet_less_equal_left

theorem meet_less_equal_right [SemilatticeMeet α] (a b : α) : a ⊓ b ≤ b :=
  (SemilatticeMeet.meet a b).meet_less_equal_right

theorem meet_greatest_lower_bound [SemilatticeMeet α] {a b c : α} : c ≤ a → c ≤ b → c ≤ a ⊓ b :=
  (SemilatticeMeet.meet a b).meet_greatest_lower_bound

instance OrderDual.instanceSupremum (α : Type u) [Infimum α] : Supremum αᵒᵈ where
  supremum := (Infimum.infimum : α → α → α)

instance OrderDual.instanceInfimum (α : Type u) [Supremum α] : Infimum αᵒᵈ where
  infimum := (Supremum.supremum : α → α → α)

instance OrderDual.instanceSemilatticeJoin [SemilatticeMeet α] : SemilatticeJoin αᵒᵈ where
  join _ _ := 
    let less_equal_join_left := @meet_less_equal_left α _ _ _
    let less_equal_join_right := @meet_less_equal_right α _ _ _
    Join.mk less_equal_join_left less_equal_join_right meet_greatest_lower_bound

instance OrderDual.instanceSemilatticeMeet [SemilatticeJoin α] : SemilatticeMeet αᵒᵈ where
  meet _ _ := 
    let meet_less_equal_left := @less_equal_join_left α _ _ _
    let meet_less_equal_right := @less_equal_join_right α _ _ _
    Meet.mk meet_less_equal_left meet_less_equal_right join_least_upper_bound

theorem meet_less_equal_of_left_less_equal [SemilatticeMeet α] {a b c : α} (h : a ≤ c) : a ⊓ b ≤ c :=
  less_equal_transitive (meet_less_equal_left a b) h

theorem meet_less_equal_of_right_less_equal [SemilatticeMeet α] {a b c : α} (h : b ≤ c) : a ⊓ b ≤ c :=
  less_equal_transitive (meet_less_equal_right a b) h

theorem less_equal_meet_equivalent [SemilatticeMeet α] {a b c : α} : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
  @join_less_equal_equivalent αᵒᵈ _ _ _ _

theorem meet_equal_left [SemilatticeMeet α] {a b : α} : a ⊓ b = a ↔ a ≤ b := by
  apply less_equal_antisymmetric_equivalent_equal.trans
  simp [less_equal_meet_equivalent, less_equal_reflexive a, meet_less_equal_left]

theorem meet_equal_right [SemilatticeMeet α] {a b : α} : a ⊓ b = b ↔ b ≤ a := by
  apply less_equal_antisymmetric_equivalent_equal.trans
  simp [less_equal_meet_equivalent, less_equal_reflexive b, meet_less_equal_right]

theorem meet_idempotent [SemilatticeMeet α] {a : α} : a ⊓ a = a := @join_idempotent αᵒᵈ _ _

theorem meet_commutative [SemilatticeMeet α] {a b : α} : a ⊓ b = b ⊓ a := @join_commutative αᵒᵈ _ _ _

theorem meet_associative [SemilatticeMeet α] {a b c : α} : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) := @join_associative αᵒᵈ _ _ _ _

theorem meet_unique [PartialOrder α] {a b j k : α} : Meet a b j → Meet a b k → j = k := by
  intro ⟨haj, hbj, hj⟩ ⟨hak, hbk, hk⟩
  have hjk := hj hak hbk
  have hkj := hk haj hbj
  exact less_equal_antisymmetric hkj hjk 

class Lattice (α : Type u) extends SemilatticeJoin α, SemilatticeMeet α

instance OrderDual.instanceLattice (α) [Lattice α] : Lattice αᵒᵈ where
  meet := OrderDual.instanceSemilatticeMeet.meet
  join := OrderDual.instanceSemilatticeJoin.join

theorem meet_less_equal_join [Lattice α] (a b : α) : a ⊓ b ≤ a ⊔ b :=
  less_equal_transitive (meet_less_equal_left a b) (less_equal_join_left a b)

theorem join_less_equal_meet_equivalent_equal [Lattice α] {a b : α} : a ⊔ b ≤ a ⊓ b ↔ a = b := by
  simp [less_equal_antisymmetric_equivalent_equal, less_equal_meet_equivalent, join_less_equal_equivalent, 
    And.associative, less_equal_reflexive a, less_equal_reflexive b, And.commutative]

def minimum [DecidableTotalOrder α] (a b : α) := if a ≤ b then a else b

def minimum_definition [DecidableTotalOrder α] (a b : α) : 
    minimum a b = if a ≤ b then a else b := 
  rfl

def maximum [DecidableTotalOrder α] (a b : α) := if a ≤ b then b else a

def maximum_definition [DecidableTotalOrder α] (a b : α) : 
    maximum a b = if a ≤ b then b else a :=
  rfl

instance instanceMaximumSemilatticeJoin [DecidableTotalOrder α] : SemilatticeJoin α where
  supremum := maximum
  join a b := 
    let less_equal_join_left := by
      if h : a ≤ b then
        simp [maximum_definition, h]
      else
        simp [maximum_definition, h, less_equal_reflexive a]
    let less_equal_join_right := by
      if h : a ≤ b then
        simp [maximum_definition, h, less_equal_reflexive b]
      else
        simp [maximum_definition, h, less_equal_of_not_greater_equal h]
    let join_least_upper_bound := by
      intro c hac hbc
      simp [maximum_definition]
      if h : a ≤ b then
        simp [h, hbc]
      else
        simp [h, hac]
    Join.mk less_equal_join_left less_equal_join_right join_least_upper_bound

instance instanceMinimumSemilatticeMeet [DecidableTotalOrder α] : SemilatticeMeet α where
  infimum := minimum
  meet a b := 
    let meet_less_equal_left := by
      if h : a ≤ b then
        simp [minimum_definition, h, less_equal_reflexive a]
      else
        simp [minimum_definition, h, less_equal_of_not_greater_equal h]
    let meet_less_equal_right := by
      if h : a ≤ b then
        simp [minimum_definition, h]
      else
        simp [minimum_definition, h, less_equal_reflexive b]
    let meet_greatest_lower_bound := by
      intro c hca hbc
      simp [minimum_definition]
      if hab : a ≤ b then
        simp [hab, hca]
      else
        simp [hab, hbc]
    Meet.mk meet_less_equal_left meet_less_equal_right meet_greatest_lower_bound

instance instanceMinimumMaximumLattice [DecidableTotalOrder α] : Lattice α where
  meet := instanceMinimumSemilatticeMeet.meet
  join := instanceMaximumSemilatticeJoin.join

@[simp]
def maximum_join [DecidableTotalOrder α] (a b : α) : maximum a b = a ⊔ b := rfl

@[simp]
def minimum_meet [DecidableTotalOrder α] (a b : α) : minimum a b = a ⊓ b := rfl

def Monotone [Preorder α] [Preorder β] (f : α → β) := ∀ {a b : α}, a ≤ b → f a ≤ f b

def Antitone [Preorder α] [Preorder β] (f : α → β) := ∀ {a b : α}, a ≤ b → f b ≤ f a

def StrictMonotone [StrictPartialOrder α] [StrictPartialOrder β] (f : α → β) := ∀ {a b : α}, a < b → f a < f b

def StrictAntitone [StrictPartialOrder α] [StrictPartialOrder β] (f : α → β) := ∀ {a b : α}, a < b → f b < f a
