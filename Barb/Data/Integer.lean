import Barb.Algebra
import Barb.Syntax
import Barb.Data.Natural

open Natural (zero successor)

def integerEquivalent : (ℕ × ℕ) → (ℕ × ℕ) → Prop
  | (n, m), (n', m') => n + m' = n' + m
  
theorem integerEquivalent.reflexive (x : ℕ × ℕ) : integerEquivalent x x := rfl
  
theorem integerEquivalent.symmetric : ∀ {x y}, (integerEquivalent x y) → (integerEquivalent y x) := Eq.symm


-- TODO: REALLY need to learn how to use the simplifier
-- TODO: Change a b c to (n, m), (n', m'), and (n'', and m'')
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

def canonicalize : (ℕ × ℕ) → (ℕ × ℕ)
  | (n, m) => match compare n m with
    | Ordering.lt => (0, m - n)
    | Ordering.eq => (0, 0)
    | Ordering.gt => (n - m, 0)

theorem canonicalize_congruent (a b : ℕ × ℕ) (h_equivalent : a ≈ b) : canonicalize a = canonicalize b := by
  let ⟨n, m⟩ := a
  let ⟨k, l⟩ := b
  have : n + l = k + m := h_equivalent
  unfold canonicalize
  split; split
  . sorry
  . sorry
  . sorry
  
instance Zero : Integer := Quotient.mk' (0, 0)

instance One : Integer := Quotient.mk' (1, 0)

def negate : ℤ → ℤ := 
  -- let negate' := λ ((n, m) : ℕ × ℕ) => Quotient.mk' (m, n)
  Quotient.map 
  -- let negate' := λ ((n, m) : ℕ × ℕ) => Quotient.mk' (m, n)
  -- let respects : ∀ a b, 
    -- a ≈ b → (negate' ∘ canonicalize) a = (negate' ∘ canonicalize) b :=
    -- λ a b h => congrArg negate' (canonicalize_congruent a b h)
  -- Quotient.lift (negate' ∘ canonicalize) respects

@[default_instance mid]
instance : Neg Integer where
  neg := negate

def add : ℤ → ℤ → ℤ :=
  let add' := λ ((n, m) : ℕ × ℕ) ((k, l) : ℕ × ℕ) => Quotient.mk' (n + k, m + l)
  let lifts := sorry
  Quotient.lift₂ add' lifts

end Integer
