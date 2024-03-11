import Barb.Algebra
import Barb.Data.Integer
import Barb.Data.Option
import Barb.Logic

open Integer (NonZeroInteger)

def RationalEquivalent : (ℤ × NonZeroInteger) → (ℤ × NonZeroInteger) → Prop
  | (a, ⟨b, _⟩), (a', ⟨b', _⟩) => a * b' = a' * b

theorem RationalEquivalent.reflexive : Relation.Reflexive RationalEquivalent := 
  λ _ => rfl

theorem RationalEquivalent.symmetric : Relation.Symmetric RationalEquivalent := by
  intro (a, ⟨b, _⟩) (c, ⟨d, _⟩) (h_ab_cd : a * d = c * b)
  exact h_ab_cd.symm

theorem RationalEquivalent.transitive : Relation.Transitive RationalEquivalent := by
  intro (a, ⟨b, b_nonzero⟩) (c, ⟨d, d_nonzero⟩) (e, ⟨f, _⟩)
  intro (h_ab_cd : a * d = c * b) (h_cd_ef : c * f = e * d)
  show a * f = e * b
  cases Integer.decideEqual c 0 with
  | isTrue c_zero =>
    have ad_zero := c_zero ▸ h_ab_cd
    rw [Integer.zero_multiply] at ad_zero
    have a_zero := Or.resolve_right (Integer.equal_zero_of_multiply_equal_zero ad_zero) d_nonzero
    have ed_zero := c_zero ▸ h_cd_ef
    rw [Integer.zero_multiply] at ed_zero
    have e_zero := Or.resolve_right (Integer.equal_zero_of_multiply_equal_zero ed_zero.symm) d_nonzero
    simp [a_zero, e_zero, Integer.multiply_zero, Integer.zero_multiply]
  | isFalse c_nonzero =>
    have h_equal := calc
      (c * d) * (a * f) = (c * f) * (a * d) := by simp [Integer.multiply_associative, Integer.multiply_commutative, Integer.multiply_left_commutative]
      _ = (e * d) * (a * d) := congrArg (. * _) h_cd_ef
      _ = (e * d) * (c * b) := congrArg (_ * .) h_ab_cd
      _ = (c * d) * (e * b) := by simp [Integer.multiply_associative, Integer.multiply_commutative, Integer.multiply_left_commutative]
    have cd_nonzero := Integer.multiply_not_equal_zero_of_not_equal_zero c_nonzero d_nonzero
    exact Integer.multiply_left_cancel h_equal cd_nonzero

theorem RationalEquivalent.is_equivalence : Equivalence RationalEquivalent :=
  { refl := RationalEquivalent.reflexive, symm := RationalEquivalent.symmetric, trans := RationalEquivalent.transitive }

instance instanceHasEquivRationalEquivalent : HasEquiv (Integer × NonZeroInteger) where
  Equiv := RationalEquivalent
  
instance instanceSetoidRationalEquivalent : Setoid (Integer × NonZeroInteger) where
  r := RationalEquivalent
  iseqv := RationalEquivalent.is_equivalence

@[simp] def RationalEquivalent.definition : (x ≈ y) = RationalEquivalent x y := rfl

instance decideRationalEquivalent (x y : ℤ × NonZeroInteger) : Decidable (x ≈ y) := 
  let (a, ⟨b, _⟩) := x
  let (c, ⟨d, _⟩) := y
  Integer.decideEqual (a * d) (c * b)

instance decideRationalEquivalentQuotientEqual : DecidableEq (Quotient instanceSetoidRationalEquivalent) := 
  inferInstance

def Rational := Quotient instanceSetoidRationalEquivalent

namespace Rational

notation "ℚ" => Rational

instance decideEqual : DecidableEq Rational := decideRationalEquivalentQuotientEqual

instance : OfNat Rational n where
  ofNat := ⟦(Integer.ofNatural (Natural.natToNatural n), ⟨1, by decide⟩)⟧
  
instance zero : Rational := ⟦(0, ⟨1, by decide⟩)⟧

@[simp]
theorem zero_definition : (0 : ℚ) = Quotient.mk instanceSetoidRationalEquivalent (0, ⟨1, by decide⟩) := rfl

instance one : Rational := ⟦(1, ⟨1, by decide⟩)⟧

@[simp]
theorem one_definition : (1 : ℚ) = Quotient.mk instanceSetoidRationalEquivalent (1, ⟨1, by decide⟩) := rfl

def add : ℚ → ℚ → ℚ :=
  let add' := λ 
  ((a, ⟨b, b_nonzero⟩) : ℤ × NonZeroInteger) 
  ((c, ⟨d, d_nonzero⟩) : ℤ × NonZeroInteger) => 
  let bd_nonzero := Integer.multiply_not_equal_zero_of_not_equal_zero b_nonzero d_nonzero
  (a*d + c*b, ⟨b*d, bd_nonzero⟩)
  Quotient.map₂ add' <| by
  intro (a, ⟨b, b_nonzero⟩) (a', ⟨b', b'_nonzero⟩) (h₁ : a * b' = a' * b)
  intro (c, ⟨d, d_nonzero⟩) (c', ⟨d', d'_nonzero⟩) (h₂ : c * d' = c' * d)
  show (a*d + c*b) * (b'*d') = (a'*d' + c'*b') * (b*d)
  rw [Integer.right_distributive, ← Integer.multiply_associative (a * d) b' d', Integer.multiply_associative a d b', Integer.multiply_commutative d b', ← Integer.multiply_associative a b' d, h₁, Integer.multiply_commutative b' d', ← Integer.multiply_associative (c * b) d' b', Integer.multiply_associative c b d', Integer.multiply_commutative b d', ← Integer.multiply_associative c d' b, h₂, Integer.multiply_associative (a' * b) d d', Integer.multiply_commutative d d', Integer.multiply_associative a' b (d' * d), ← Integer.multiply_associative b d' d, Integer.multiply_commutative b d', Integer.multiply_associative d' b d, ← Integer.multiply_associative a' d' (b * d), Integer.multiply_associative (c' * d) b b', Integer.multiply_commutative b b', ← Integer.multiply_associative (c' * d) b' b, Integer.multiply_associative c' d b', Integer.multiply_commutative d b', ← Integer.multiply_associative c' b' d, Integer.multiply_associative (c' * b') d b, Integer.multiply_commutative d b, ← Integer.right_distributive]

instance : Add Rational where add := add

@[simp] theorem add_definition : add x y = x + y := rfl

def multiply : ℚ → ℚ → ℚ :=
  let multiply' := λ
  ((a, ⟨b, b_nonzero⟩) : ℤ × NonZeroInteger) 
  ((c, ⟨d, d_nonzero⟩) : ℤ × NonZeroInteger) => 
  let bd_nonzero := Integer.multiply_not_equal_zero_of_not_equal_zero b_nonzero d_nonzero
  (a*c, ⟨b*d, bd_nonzero⟩)
  Quotient.map₂ multiply' <| by
  intro (a, ⟨b, b_nonzero⟩) (a', ⟨b', b'_nonzero⟩) (hab : a * b' = a' * b)
  intro (c, ⟨d, d_nonzero⟩) (c', ⟨d', d'_nonzero⟩) (hcd : c * d' = c' * d)
  show (a*c) * (b'*d') = (a'*c') * (b*d)
  calc
    (a*c) * (b'*d') 
      = (a*b') * (c*d') := by simp [Integer.multiply_associative, Integer.multiply_commutative, Integer.multiply_left_commutative]
    _ = (a'*b) * (c*d') := congrArg (. * _) hab
    _ = (a'*b) * (c'*d) := congrArg (_ * .) hcd
    _ = (a'*c') * (b*d) := by simp [Integer.multiply_associative, Integer.multiply_commutative, Integer.multiply_left_commutative]
    
instance : Mul Rational where mul := multiply

@[simp] theorem multiply_definition : multiply x y = x * y := rfl

def negate : ℚ → ℚ :=
  let negate' := λ ((a, ⟨b, b_nonzero⟩) : ℤ × NonZeroInteger) => (-a, ⟨b, b_nonzero⟩)
  Quotient.map negate' <| by
  intro (a, ⟨b, b_nonzero⟩) (a', ⟨b', b'_nonzero⟩) (h : a*b' = a'*b)
  show (-a)*b' = (-a')*b
  rw [← Integer.negate_multiply_equal_negate_multiply, h, Integer.negate_multiply_equal_negate_multiply]

instance : Neg Rational where neg := negate

@[simp] theorem negate_definition : negate x = -x := rfl
  
abbrev NonZeroRational := {x : ℚ // x ≠ 0}

def preReciprocal : ℤ × NonZeroInteger → Option ℚ
  | (a, ⟨b, _⟩) => if ha : a ≠ 0 then some ⟦(b, ⟨a, ha⟩)⟧ else none
  
@[simp]
theorem preReciprocal_none (x : ℤ × NonZeroInteger) (h : x.1 = 0) : preReciprocal x = none := by
  simp [preReciprocal, h]

@[simp]
theorem preReciprocal_some (x : ℤ × NonZeroInteger) (h : x.1 ≠ 0) :
    preReciprocal x = some ⟦(x.2.1, ⟨x.1, h⟩)⟧ := by
  simp [preReciprocal, h]
  
theorem numerator_nonzero_of_nonzero : ∀ {x : ℤ × NonZeroInteger}, ⟦x⟧ ≠ (0 : ℚ) → x.1 ≠ 0 := by
  intro (a, ⟨b, b_nonzero⟩) h
  have h' : Quotient.mk instanceSetoidRationalEquivalent (a, ⟨b, b_nonzero⟩) ≠ (0 : ℚ) := h
  intro ha
  simp at ha
  apply (absurd . h')
  apply Quotient.sound
  show a * 1 = 0 * b
  simp [ha, Integer.zero_multiply, Integer.multiply_zero]

def reciprocal' : ℚ → Option ℚ :=
  Quotient.lift preReciprocal <| by
  intro ⟨a, b, hb⟩ ⟨c, d, hd⟩ (h : a * d = c * b)
  cases Decidable.em (a = 0)
  <;> cases Decidable.em (b = 0)
  <;> simp_all [preReciprocal, preReciprocal_none, preReciprocal_some]
  case inl.inr _ => 
    rw [Integer.zero_multiply] at h
    have := Or.resolve_right (Integer.equal_zero_of_multiply_equal_zero h.symm) hb
    simp [this]
  case inr.inr ha =>
    suffices c ≠ 0 by
    { simp [this]
      apply Quotient.sound 
      show b * c = d * a
      simp [h, Integer.multiply_commutative] }
    apply And.left
    apply Integer.not_equal_zero_of_multiply_not_equal_zero
    intro hcb
    have := Integer.multiply_not_equal_zero_of_not_equal_zero ha hd
    exact absurd (hcb.symm.trans h.symm) this.symm

def reciprocal (x : ℚ) (h : x ≠ 0) : ℚ :=
  Option.get (reciprocal' x) <| by
  have ⟨(a, ⟨b, b_nonzero⟩), hab⟩ := Quotient.exists_rep x
  have a_nonzero := numerator_nonzero_of_nonzero (hab.symm ▸ h)
  rw [← hab, reciprocal', Quotient.lift_construct, Option.isSome]
  have := preReciprocal_some ⟨a, b, b_nonzero⟩ a_nonzero
  simp [this]

theorem add_associative : ∀ (x y z : ℚ), (x + y) + z = x + (y + z) := by
  apply Quotient.ind₃
  intro (a, ⟨b, _⟩) (c, ⟨d, _⟩) (e, ⟨f, _⟩)
  apply Quotient.sound
  show ((a*d + c*b)*f + e*(b*d))*(b*(d*f)) = (a*(d*f) + (c*f + e*d)*b)*((b*d)*f)
  let n_left := ((a*d + c*b)*f + e*(b*d)); let n_right := (a*(d*f) + (c*f + e*d)*b)
  let d_left := (b*(d*f)); let d_right := ((b*d)*f)
  suffices n_left = n_right ∧ d_left = d_right by simp [this.left, this.right]
  apply And.intro
  . simp [n_left, n_right]
    rw [Integer.right_distributive, Integer.multiply_associative a d f, 
    Integer.add_associative, Integer.multiply_right_commutative, ← Integer.multiply_associative e b d, 
    Integer.multiply_right_commutative e b d, ← Integer.right_distributive]
  . exact (Integer.multiply_associative _ _ _).symm
  
theorem add_commutative : ∀ (x y : ℚ), x + y = y + x := by
  apply Quotient.ind₂
  intro (a, ⟨b, _⟩) (c, ⟨d, _⟩)
  apply Quotient.sound
  show (a*d + c*b)*(d*b) = (c*b + a*d)*(b*d)
  suffices (a*d + c*b) = (c*b + a*d) ∧ d*b = b*d by rw [this.left, this.right]
  apply And.intro (Integer.add_commutative _ _) (Integer.multiply_commutative _ _)
  
theorem add_identity : ∀ (x : ℚ), x + 0 = x := by
  apply Quotient.ind
  intro (a, ⟨b, _⟩)
  apply Quotient.sound
  show (a*1 + 0*b)*b = a*(b*1)
  simp [Integer.multiply_one, Integer.zero_multiply, Integer.add_zero]
  
theorem add_inverse : ∀ (x : ℚ), x + (-x) = 0 := by
  apply Quotient.ind
  intro (a, ⟨b, _⟩)
  apply Quotient.sound
  show (a*b + (-a)*b) * 1 = 0 * (b*b)
  rw [Integer.multiply_one, ← Integer.right_distributive, Integer.add_inverse, 
    Integer.zero_multiply, Integer.zero_multiply]

theorem multiply_associative : ∀ (x y z : ℚ), (x * y) * z = x * (y * z) := by
  apply Quotient.ind₃
  intro (a, ⟨b, _⟩) (c, ⟨d, _⟩) (e, ⟨f, _⟩)
  apply Quotient.sound
  show ((a*c)*e) * (b*(d*f)) = (a*(c*e)) * ((b*d)*f)
  simp [Integer.multiply_associative]
  
theorem multiply_commutative : ∀ (x y : ℚ), x * y = y * x := by
  apply Quotient.ind₂
  intro (a, ⟨b, _⟩) (c, ⟨d, _⟩)
  apply Quotient.sound
  show (a*c) * (d*b) = (c*a) * (b*d)
  simp [Integer.multiply_commutative]
  
theorem multiply_identity : ∀ (x : ℚ), x * 1 = x := by
  apply Quotient.ind
  intro (a, ⟨b, _⟩)
  apply Quotient.sound
  show (a*1) * b = a * (b*1)
  simp [Integer.multiply_one]

theorem left_distributive : ∀ (x y z : ℚ), x * (y + z) = x * y + x * z := by
  apply Quotient.ind₃
  intro (a, ⟨b, _⟩) (c, ⟨d, _⟩) (e, ⟨f, _⟩)
  apply Quotient.sound
  show (a*(c*f + e*d)) * ((b*d)*(b*f)) = ((a*c)*(b*f) + (a*e)*(b*d))*(b*(d*f))
  simp [Integer.multiply_associative, Integer.multiply_commutative, Integer.left_distributive, Integer.multiply_left_commutative]
  
theorem right_distributive : ∀ (x y z : ℚ), (x + y) * z = x * z + y * z := by
  intro x y z
  rw [multiply_commutative, left_distributive, multiply_commutative z x, multiply_commutative z y]

theorem multiply_inverse : ∀ (x : ℚ) (h : x ≠ 0), x * (reciprocal x h) = 1 := by
  apply Quotient.ind
  intro (a, ⟨b, b_nonzero⟩) h
  have h' := numerator_nonzero_of_nonzero h
  simp at h'
  simp [reciprocal, reciprocal']
  have h_some := (preReciprocal_some (a, ⟨b, b_nonzero⟩) h')
  simp [h_some]
  apply Quotient.sound
  show (a*b)*1 = 1*(b*a)
  simp [Integer.multiply_commutative]
  
instance field : Field Rational where
  add_associative := add_associative
  add_commutative := add_commutative
  add_identity := add_identity
  add_inverse := add_inverse

  multiply_associative := multiply_associative
  multiply_commutative := multiply_commutative
  multiply_identity := multiply_identity

  left_distributive := left_distributive
  right_distributive := right_distributive
  
  reciprocal := reciprocal
  multiply_inverse := multiply_inverse

end Rational
