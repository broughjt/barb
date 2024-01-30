import Barb.Algebra
import Barb.Quotient
import Barb.Syntax
import Barb.Data.Natural

open Natural (zero successor)

def integerEquivalent : (ℕ × ℕ) → (ℕ × ℕ) → Prop
  | (n, m), (n', m') => n + m' = n' + m

theorem integerEquivalent.reflexive (x : ℕ × ℕ) : integerEquivalent x x := rfl
  
theorem integerEquivalent.symmetric : ∀ {x y}, (integerEquivalent x y) → (integerEquivalent y x) := Eq.symm

theorem integerEquivalent.transitive : ∀ {x y z}, 
  integerEquivalent x y → integerEquivalent y z → integerEquivalent x z
  | (a, b), (c, d), (e, f), h1, h2 =>
    have h3 : a + d = c + b := h1
    have h4 : c + f = e + d := h2
    have h5 := calc
      (a + d) + (c + f) = (c + b) + (c + f) := congrArg (. + (c + f)) h3
      _                 = (c + b) + (e + d) := congrArg ((c + b) + .) h4
    have h6 := calc
      (a + d) + (c + f) = (d + a) + (c + f) := congrArg (. + (c + f)) (Natural.add_commutative a d)
      _ = d + (a + (c + f)) := Natural.add_associative d a (c + f)
      _ = d + ((a + c) + f) := congrArg (d + .) (Natural.add_associative a c f).symm
      _ = d + ((c + a) + f) := congrArg (λ x => d + (x + f)) (Natural.add_commutative a c)
      _ = d + (c + (a + f)) := congrArg (d + .) (Natural.add_associative c a f)
      _ = (d + c) + (a + f) := (Natural.add_associative d c (a + f)).symm
      _ = (c + d) + (a + f) := congrArg (. + (a + f)) (Natural.add_commutative d c)
    have h7 := calc
      (c + b) + (e + d) = (c + b) + (d + e) := congrArg ((c + b) + .) (Natural.add_commutative e d)
      _ = ((c + b) + d) + e := (Natural.add_associative (c + b) d e).symm
      _ = (c + (b + d)) + e := congrArg (. + e) (Natural.add_associative c b d)
      _ = (c + (d + b)) + e := congrArg (λ x => (c + x) + e) (Natural.add_commutative b d)
      _ = ((c + d) + b) + e := congrArg (. + e) (Natural.add_associative c d b).symm
      _ = (c + d) + (b + e) := Natural.add_associative (c + d) b e
      _ = (c + d) + (e + b) := congrArg ((c + d) + .) (Natural.add_commutative b e)
    have : (c + d) + (a + f) = (c + d) + (e + b) := (h6.symm.trans h5).trans h7
    Natural.add_left_cancel this

theorem integerEquivalence.is_equivalence : Equivalence integerEquivalent :=
  { refl := integerEquivalent.reflexive, symm := integerEquivalent.symmetric, trans := integerEquivalent.transitive }

instance instanceHasEquivIntegerEquivalent : HasEquiv (ℕ × ℕ) where
  Equiv := integerEquivalent
  
instance instanceSetoidIntegerEquivalent : Setoid (ℕ × ℕ) where
  r := integerEquivalent
  iseqv := integerEquivalence.is_equivalence

def Integer := Quotient instanceSetoidIntegerEquivalent

namespace Integer

notation "ℤ" => Integer

-- instance : Coe Natural Integer := ⟨Integer.ofNatural⟩

instance : OfNat Integer n where
  ofNat := Quotient.mk' (Natural.natToNatural n, 0)

instance Zero : Integer := Quotient.mk' (0, 0)

instance One : Integer := Quotient.mk' (1, 0)

def negate : ℤ → ℤ := 
  let negate' := λ ((n, m) : ℕ × ℕ) => (m, n)
  Quotient.map negate' <| by
  intro (n, m) (n', m') (h_equivalent : n + m' = n' + m)
  show m + n' = m' + n
  simp [Natural.add_commutative, h_equivalent]

instance : Neg Integer where
  neg := negate

def add : ℤ → ℤ → ℤ :=
  let add' := λ ((n, m) : ℕ × ℕ) ((k, l) : ℕ × ℕ) => (n + k, m + l)
  Quotient.map₂ add' <| by
  intro (n, m) (n', m') (h1 : n + m' = n' + m)
  intro (k, l) (k', l') (h2 : k + l' = k' + l)
  show (n + k) + (m' + l') = (n' + k') + (m + l)
  calc
    (n + k) + (m' + l') = ((n + k) + m') + l' := (Natural.add_associative (n + k) m' l').symm
    _ = (n + (k + m')) + l' := congrArg (. + l') (Natural.add_associative n k m')
    _ = (n + (m' + k)) + l' := congrArg (λ x => (n + x) + l') (Natural.add_commutative k m')
    _ = ((n + m') + k) + l' := congrArg (. + l') (Natural.add_associative n m' k).symm
    _ = ((n' + m) + k) + l' := congrArg (λ x => (x + k) + l') h1
    _ = (n' + m) + (k + l') := Natural.add_associative (n' + m) k l'
    _ = (n' + m) + (k' + l) := congrArg ((n' + m) + .) h2
    _ = ((n' + m) + k') + l := (Natural.add_associative (n' + m) k' l).symm
    _ = (n' + (m + k')) + l := congrArg (. + l) (Natural.add_associative n' m k')
    _ = (n' + (k' + m)) + l := congrArg (λ x => (n' + x) + l) (Natural.add_commutative m k')
    _ = ((n' + k') + m) + l := congrArg (. + l) (Natural.add_associative n' k' m).symm
    _ = (n' + k') + (m + l) := Natural.add_associative (n' + k') m l

instance : Add Integer where add := add

theorem add_commutative : ∀ (a b : ℤ), a + b = b + a := by
  apply Quotient.ind₂
  intro (n, m) (k, l)
  apply Quotient.sound
  show (n + k) + (l + m) = (k + n) + (m + l)
  simp [Natural.add_commutative]

theorem add_associative : ∀ (a b c : ℤ), (a + b) + c = a + (b + c) := by
  intro a b c
  -- TODO: ind₃
  let i := Quotient.mk instanceSetoidIntegerEquivalent
  suffices ∀ (a b c : ℕ × ℕ), add (add (i a) (i b)) (i c) = add (i a) (add (i b) (i c)) from Quotient.inductionOn₃ a b c this
  intro (n, m) (k, l) (o, p)
  apply Quotient.sound
  show ((n + k) + o) + (m + (l + p)) = (n + (k + o)) + ((m + l) + p)
  simp [Natural.add_associative]

theorem add_identity : ∀ (a : ℤ), a + 0 = a := by
  apply Quotient.ind
  intro (n, m)
  apply Quotient.sound
  show (n + 0) + m = n + (m + 0)
  simp [Natural.add_zero]

theorem add_inverse : ∀ (a : ℤ), a + (-a) = 0 := by
  apply Quotient.ind
  intro (n, m)
  apply Quotient.sound
  show (n + m) + 0 = 0 + (m + n)
  simp [Natural.add_zero, Natural.zero_add, Natural.add_commutative]
