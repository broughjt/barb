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
    have cd_nonzero := Integer.multiply_nonzero_of_nonzero c_nonzero d_nonzero
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
  ofNat := ⟦(Integer.ofNatural (Natural.fromNat n), ⟨1, by decide⟩)⟧

instance zero : Rational := ⟦(0, ⟨1, by decide⟩)⟧

theorem zero_definition : (0 : ℚ) = Quotient.mk instanceSetoidRationalEquivalent (0, ⟨1, by decide⟩) := rfl

instance one : Rational := ⟦(1, ⟨1, by decide⟩)⟧

theorem one_definition : (1 : ℚ) = Quotient.mk instanceSetoidRationalEquivalent (1, ⟨1, by decide⟩) := rfl

def add : ℚ → ℚ → ℚ :=
  let add' := λ
  ((a, ⟨b, b_nonzero⟩) : ℤ × NonZeroInteger)
  ((c, ⟨d, d_nonzero⟩) : ℤ × NonZeroInteger) =>
  let bd_nonzero := Integer.multiply_nonzero_of_nonzero b_nonzero d_nonzero
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
  let bd_nonzero := Integer.multiply_nonzero_of_nonzero b_nonzero d_nonzero
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
    apply Integer.nonzero_of_multiply_nonzero
    intro hcb
    have := Integer.multiply_nonzero_of_nonzero ha hd
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

theorem add_zero : ∀ (x : ℚ), x + 0 = x := by
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

theorem multiply_one : ∀ (x : ℚ), x * 1 = x := by
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
  add_zero := add_zero
  add_inverse := add_inverse

  multiply_associative := multiply_associative
  multiply_commutative := multiply_commutative
  multiply_one := multiply_one

  left_distributive := left_distributive
  right_distributive := right_distributive

  reciprocal := reciprocal
  multiply_inverse := multiply_inverse

def subtract (x y : ℚ) : ℚ := x + (-y)

instance : Sub Rational where sub := subtract

@[simp]
theorem subtract_definition (x y : ℚ) : x + (-y) = x - y := rfl

def divide (x y : ℚ) (y_nonzero : y ≠ 0) : ℚ := x * (reciprocal y y_nonzero)

theorem negate_involutive : Function.Involutive negate := by
  apply Quotient.ind
  intro (a, ⟨b, b_nonzero⟩)
  apply Quotient.sound
  show (- - a)*b = a * b
  rw [Integer.negate_negate]

@[simp]
theorem negate_negate : ∀ x : ℚ, - -x = x := λ x => negate_involutive x

-- TODO: Copy pasted from Integers, this is all general to rings I think
-- Lesson (worth writing about): If you start building up a collection theorems which only appeal to a few lemmas you proved earlier, it's time to abstract because you are dealing with a more general structure of which your original type is an example

theorem zero_add (a : ℚ) : 0 + a = a := by
  rw [add_commutative, add_zero]

theorem multiply_zero : ∀ (a : ℚ), a * 0 = 0 := by
  apply Quotient.ind
  intro (n, m)
  apply Quotient.sound
  show (n * 0) * 1 = 0 * (m * 1)
  simp [Integer.multiply_zero, Integer.zero_multiply]

theorem zero_multiply (a : ℚ) : 0 * a = 0 := by
  rw [multiply_commutative, multiply_zero]

theorem one_multiply (a : ℚ) : 1 * a = a := by
  rw [multiply_commutative, multiply_one]

theorem add_left_commutative (n m k : ℚ) : n + (m + k) = m + (n + k) := by
  rw [← add_associative, add_commutative n m, add_associative]

theorem add_right_commutative (n m k : ℚ) : (n + m) + k = (n + k) + m := by
  rw [add_associative, add_commutative m k, ← add_associative]

theorem add_inverse_left (a : ℚ) : -a + a = 0 := by
  rw [add_commutative, add_inverse]

theorem add_left_cancel {a b c : ℚ} (h : a + b = a + c) : b = c := by
  have : -a + (a + b) = -a + (a + c) := by rw [h]
  simp [← add_associative, add_inverse_left, zero_add] at this
  exact this

theorem add_right_cancel {a b c : ℚ} (h : a + c = b + c) : a = b := by
  rewrite [add_commutative a c, add_commutative b c] at h
  exact add_left_cancel h

theorem negate_add_cancel_left (a b : ℚ) : -a + (a + b) = b := by
  rw [← add_associative (-a) a b, add_inverse_left, zero_add]

theorem negate_add_cancel_right (a b : ℚ) : (a + -b) + b = a := by
  rw [add_associative, add_inverse_left, add_zero]

theorem add_negate_cancel_left (a b : ℚ) : a + (-a + b) = b := by
  rw [← add_associative, add_inverse, zero_add]

theorem add_negate_cancel_right (a b : ℚ) : (a + b) + -b = a := by
  rw [add_associative, add_inverse, add_zero]

theorem negate_zero : (0 : ℚ) = (-0 : ℚ) := rfl

theorem subtract_self (a : ℚ) : a - a = 0 := add_inverse a

theorem subtract_zero (a : ℚ) : a - 0 = a := by
  rw [← subtract_definition, ← negate_zero, add_zero]

theorem zero_subtract (a : ℚ) : 0 - a = -a := by
  rw [← subtract_definition, zero_add]

theorem negate_equal_of_add_equal_zero {a b : ℚ} (h : a + b = 0) : a = -b := by
  rw [← add_zero a, ← add_inverse (b), ← add_associative, h, zero_add]

theorem subtract_equal_zero_of_equal {a b : ℚ} (h : a = b) : a - b = 0 := by
  rw [← h, subtract_self]

theorem equal_of_subtract_equal_zero {a b : ℚ} (h : a - b = 0) : a = b := by
  rw [← add_zero a, ← add_inverse b, add_commutative b, ← add_associative, subtract_definition, h, zero_add]

theorem negate_add (a b : ℚ) : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_inverse, add_associative, ← add_associative b (-a) (-b), add_commutative b (-a),
     ← add_associative a, ← add_associative, add_inverse, zero_add, add_inverse]

theorem subtract_subtract (a b c : ℚ) : (a - b) - c = a - (b + c) := by
  apply Eq.symm
  rw [← subtract_definition, negate_add, ← add_associative, subtract_definition, subtract_definition]

theorem negate_subtract {a b : ℚ} : -(a - b) = b - a := by
  calc
    -(a - b) = -(a + -b) := rfl
    _ = -a + (- -b) := negate_add a (-b)
    _ = -a + b := congrArg (_ + .) (negate_negate _)
    _ = b + -a := add_commutative _ _
    _ = b - a := subtract_definition _ _

theorem subtract_subtract_self (a b : ℚ) : a - (a - b) = b := by
  rw [← subtract_definition, negate_subtract, ← subtract_definition,
    add_commutative (b) (-a), add_negate_cancel_left]

-- Looked at proof in lean std which uses negate_equal_of_add_equal_zero. This was foreign to me.
-- Observation is that conclusion is of the form we would like here, we need a' = a * b and b' = -a * b, and then the theorem will tell us -(a * b) = -a * b, which is our desired result. So we need to provide (-(a * b)) + (-a * b) = 0, which we can do.
theorem negate_multiply_equal_negate_multiply (a b : ℚ) : -(a * b) = -a * b := by
  apply Eq.symm
  apply negate_equal_of_add_equal_zero
  rw [← right_distributive, add_commutative, add_inverse, zero_multiply]

theorem negate_multiply_equal_multiply_negate (a b : ℚ) : -(a * b) = a * -b := by
  rw [multiply_commutative, negate_multiply_equal_negate_multiply, multiply_commutative]

-- End copy pasted nonsense from integers, need to generalize to rings and fields

-- Why does Tao elect to define less than before less equal?

/-
def LessEqual (x y : ℚ) : Prop :=
  -- TODO: rename nonnegative
  let positive'
    | u => ∃ v : Integer.NonNegativeInteger × Integer.PositiveInteger, u ≈ (v.1.val, ⟨v.2.val, (not_equal_of_less_than v.2.property).symm⟩)
  Quotient.liftOn (y - x) positive' <| by
  intro a b (h : a ≈ b)
  apply propext
  apply Iff.intro
  . simp
    intro ⟨v, hv⟩
    apply Exists.intro v (h.symmetric.transitive hv)
  . simp
    intro ⟨v, hv⟩
    apply Exists.intro v (h.transitive hv)

theorem LessEqual.reflexive : Relation.Reflexive LessEqual := by
  unfold LessEqual
  intro x
  rw [subtract_self, zero_definition, Quotient.lift_construct_on]
  exact Exists.intro (⟨0, by decide⟩, ⟨1, by decide⟩) rfl

-- TODO: Don't try to simplify, work out on paper what the show statement needs to be and prove that
theorem LessEqual.antisymmetric : Relation.AntiSymmetric LessEqual := by
  unfold Relation.AntiSymmetric
  unfold LessEqual
  apply Quotient.ind₂
  intro ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩
  intro ⟨(⟨s, hs⟩, ⟨t, ht⟩), hst'⟩ ⟨(⟨u, hu⟩, ⟨v, hv⟩), huv'⟩
  have hst : (c*b + -a*d)*t = s * (d*b) := hst'
  have huv : (a*d + -c*b)*v = u*(b*d) := huv'
  apply Quotient.sound
  show a*d = c*b
-/

def LessThan (x y : ℚ) : Prop :=
  let positive'
    | (a, ⟨b, b_nonzero⟩) => ∃ v : Integer.PositiveInteger × Integer.PositiveInteger,
      let (⟨c, _⟩, ⟨d, d_positive⟩) := v;
      RationalEquivalent (a, ⟨b, b_nonzero⟩) (c, ⟨d, (not_equal_of_less_than d_positive).symm⟩)
  Quotient.liftOn (y - x) positive' <| by
  intro a b (h : a ≈ b)
  apply propext
  apply Iff.intro
  . simp
    intro ⟨v, hv⟩
    apply Exists.intro v (h.symmetric.transitive hv)
  . simp
    intro ⟨v, hv⟩
    apply Exists.intro v (h.transitive hv)

instance : LT Rational where
  lt := LessThan

@[simp] theorem less_than_definition : (x < y) = (LessThan x y) := rfl

theorem LessThan.irreflexive : Relation.Irreflexive LessThan := by
  intro x
  unfold LessThan
  simp
  rw [subtract_self, zero_definition, Quotient.lift_construct_on]
  intro ⟨(⟨a, a_positive⟩, ⟨b, _⟩), (hv : 0 * b = a * 1)⟩
  rw [Integer.zero_multiply, Integer.multiply_one] at hv
  exact absurd hv (not_equal_of_less_than a_positive)
  
-- TODO: Rename all these to just use lowercase like everything else, there's no good reason to use the projection naming like this, it just looks weird at every callsite

-- Here we appeal to asymmetry of less than on the integers. We suppose both x < y and y < x, lower these statements to statements about integer representatives for x and y, and then show that supposing both contradicts the asymmetry property of the less than relation for the integers.
-- TODO: Don't need this
/-
theorem LessThan.asymmetric : Relation.Asymmetric LessThan := by
  apply Quotient.ind₂
  intro ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩
  intro ⟨(⟨u, u_positive⟩, ⟨v, v_positive⟩), (huv : (c*b + -a*d)*v = u*(d*b))⟩
  intro ⟨(⟨s, s_positive⟩, ⟨t, t_positive⟩), (hst : (a*d + -c*b)*t = s*(b*d))⟩
  rw [Integer.multiply_commutative d b, ← Integer.negate_multiply_equal_negate_multiply] at huv
  rw [← Integer.negate_multiply_equal_negate_multiply] at hst
  match less_than_trichotomous (b*d) 0 with
  | Or.inl bd_negative =>
    have hcbad := Integer.less_than_of_subtract_negative <|
      Integer.negative_left_of_multiply_negative_of_positive_right
      (huv.symm ▸ Integer.multiply_negative_of_positive_of_negative u_positive bd_negative) v_positive
    have hadcb := Integer.less_than_of_subtract_negative <|
      Integer.negative_left_of_multiply_negative_of_positive_right
      (hst.symm ▸ Integer.multiply_negative_of_positive_of_negative s_positive bd_negative) t_positive
    exact absurd hcbad (less_than_asymmetric hadcb)
  | Or.inr (Or.inl bd_zero) =>
    exact absurd bd_zero (Integer.multiply_nonzero_of_nonzero b_nonzero d_nonzero)
  | Or.inr (Or.inr bd_positive) =>
    have hadcb := Integer.less_than_of_subtract_positive <|
      Integer.positive_left_of_multiply_positive_of_positive_right 
      (huv.symm ▸ Integer.multiply_positive u_positive bd_positive) v_positive
    have hcbad := Integer.less_than_of_subtract_positive <| 
      Integer.positive_left_of_multiply_positive_of_positive_right
      (hst.symm ▸ Integer.multiply_positive s_positive bd_positive) t_positive
    exact absurd hadcb (less_than_asymmetric hcbad)
-/
    
-- Readable proof of this and asymmetric property are in the last few pages of black notebook, we should turn them into latex. Gist for this one is just to plug in one equation into the other
-- This proof is easy once you write out the equations in terms of fractions like c//d - a//b = p//q and solve.
-- TODO: Is it possible to avoid the case split on c = 0? I think it's gotta be, the equations are the same at the end
theorem LessThan.transitive : Relation.Transitive LessThan := by
  apply Quotient.ind₃
  intro ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩ ⟨e, f, f_nonzero⟩
  intro ⟨(⟨p, p_positive⟩, ⟨q, q_positive⟩), (hpq : (c*b + -a*d)*q = p*(d*b))⟩
  intro ⟨(⟨s, s_positive⟩, ⟨t, t_positive⟩), (hst : (e*d + -c*f)*t = s*(f*d))⟩
  match (Decidable.em (c = 0)) with
  | Or.inl c_zero =>
    rw [c_zero, Integer.zero_multiply, Integer.zero_add, Integer.multiply_associative, Integer.multiply_left_commutative, ← Integer.negate_multiply_equal_negate_multiply, Integer.multiply_left_commutative p _ _] at hpq
    have hpq' := Integer.multiply_left_cancel hpq d_nonzero
    rw [c_zero, ← Integer.negate_zero, Integer.zero_multiply, Integer.add_zero, Integer.multiply_associative, Integer.multiply_left_commutative, ← Integer.multiply_associative s _ _, Integer.multiply_commutative _ d] at hst
    have hst' := Integer.multiply_left_cancel hst d_nonzero
    have : (e*t)*(b*q) + (-(a*q))*(f*t) = (s*f)*(b*q) + (p*b)*(f*t) := by simp [hpq', hst']
    have hetbq : e*t*(b*q) = (e*b) * (q*t) := by simp [Integer.multiply_commutative, Integer.multiply_left_commutative]
    have haqft : (a*q)*(f*t) = (a*f)*(q*t) := by simp [Integer.multiply_commutative, Integer.multiply_left_commutative]
    have hsfbq : (s*f)*(b*q) = (s*q)*(f*b) := by simp [Integer.multiply_commutative, Integer.multiply_left_commutative]
    have hpbft : (p*b)*(f*t) = (p*t)*(f*b) := by simp [Integer.multiply_commutative, Integer.multiply_left_commutative]
    rw [hetbq, ← Integer.negate_multiply_equal_negate_multiply, haqft, Integer.negate_multiply_equal_negate_multiply, Integer.negate_multiply_equal_negate_multiply, hsfbq, hpbft, ← Integer.right_distributive, ← Integer.right_distributive] at this
    let qt : Integer.PositiveInteger := ⟨q*t, Integer.multiply_positive q_positive t_positive⟩
    let sqpt : Integer.PositiveInteger := ⟨(s * q + p * t), Integer.add_less_than_add (Integer.multiply_positive s_positive q_positive) (Integer.multiply_positive p_positive t_positive)⟩
    exact Exists.intro (sqpt, qt) this
  | Or.inr c_nonzero =>
    have hpq' := congrArg (. + (a*d*q)) hpq
    simp at hpq'
    rw [Integer.right_distributive, ← Integer.negate_multiply_equal_negate_multiply, ← Integer.negate_multiply_equal_negate_multiply, Integer.add_associative, Integer.add_inverse_left, Integer.add_zero] at hpq'
    rw [Integer.right_distributive] at hst
    have hst' := congrArg (. * (c*b*q)) hst
    simp at hst'
    have foo : e*d*t*(c*b*q) = ((c*d)*(t*q))*(e*b) := by simp [Integer.multiply_commutative, Integer.multiply_left_commutative]
    have bar : c * f * t * (a * d * q) = ((c*d)*(t*q))*(a*f) := by simp [Integer.multiply_commutative, Integer.multiply_left_commutative]
    rw [Integer.right_distributive, congrArg ((-c * f * t) * .) hpq', Integer.left_distributive, foo, Integer.add_left_commutative, ← Integer.negate_multiply_equal_negate_multiply, ← Integer.negate_multiply_equal_negate_multiply, ← Integer.negate_multiply_equal_negate_multiply] at hst'
    have dark := congrArg ((c * f * t * (p * (d * b))) + .) hst'
    simp at dark
    have poo : c * f * t * (p * (d * b)) = (f*b)*((c*d)*(t*p)) := by simp [Integer.multiply_commutative, Integer.multiply_left_commutative]
    have bear : s * (f * d) * (c * b * q) = (f*b)*((c*d)*(s*q)) := by simp [Integer.multiply_commutative, Integer.multiply_left_commutative]
    rw [Integer.add_negate_cancel_left, ← Integer.negate_multiply_equal_negate_multiply, bar, Integer.negate_multiply_equal_multiply_negate, ← Integer.left_distributive, Integer.multiply_associative, poo, bear, ← Integer.left_distributive, ← Integer.left_distributive, Integer.multiply_left_commutative (f*b) _ _] at dark
    have cd_nonzero : c*d ≠ 0 := Integer.multiply_nonzero_of_nonzero c_nonzero d_nonzero
    have kick := Integer.multiply_left_cancel dark cd_nonzero
    rw [Integer.multiply_commutative (t*q) _, Integer.multiply_commutative (f*b) _, Integer.negate_multiply_equal_negate_multiply] at kick
    have htq := Integer.multiply_positive t_positive q_positive
    have htpsq := Integer.add_less_than_add (Integer.multiply_positive t_positive p_positive) (Integer.multiply_positive s_positive q_positive)
    rw [Integer.add_zero] at htpsq
    let u : Integer.PositiveInteger := ⟨t * p + s * q, htpsq⟩
    let v : Integer.PositiveInteger := ⟨t * q, htq⟩
    exact Exists.intro (u, v) kick

theorem positive_or_negative_of_equal_positive : ∀ {a : ℤ} {b : NonZeroInteger} {c d : Integer.PositiveInteger}, 
    (a, b) ≈ (c.val, ⟨d, (not_equal_of_less_than d.property).symm⟩) →
    (0 < a ∧ 0 < b.val) ∨ (a < 0 ∧ b.val < 0) := by
  intro a ⟨b, b_nonzero⟩ ⟨c, c_positive⟩ ⟨d, d_positive⟩
  intro (h : a * d = c * b)
  simp
  match less_than_trichotomous 0 b with
  | Or.inl hb =>
    have ha := Integer.positive_left_of_multiply_positive_of_positive_right
      (h.symm ▸ Integer.multiply_positive c_positive hb) d_positive
    exact Or.inl (And.intro ha hb)
  | Or.inr (Or.inl hb) => exact absurd hb.symm b_nonzero
  | Or.inr (Or.inr hb) =>
    have ha := Integer.negative_left_of_multiply_negative_of_positive_right
      (h.symm ▸ Integer.multiply_negative_of_positive_of_negative c_positive hb) d_positive
    exact Or.inr (And.intro ha hb)
  skip

theorem equal_positive_of_positive_or_negative : ∀ {a : ℤ} {b : NonZeroInteger},
    (0 < a ∧ 0 < b.val) ∨ (a < 0 ∧ b.val < 0) →
    ∃ u : Integer.PositiveInteger × Integer.PositiveInteger,
      let (⟨c, _⟩, ⟨d, d_positive⟩) := u
      (a, b) ≈ (c, ⟨d, (not_equal_of_less_than d_positive).symm⟩)
  | a, ⟨b, _⟩, Or.inl ⟨a_positive, b_positive⟩ =>
    Exists.intro (⟨a, a_positive⟩, ⟨b, b_positive⟩) (RationalEquivalent.reflexive _)
  | a, ⟨b, _⟩, Or.inr ⟨a_negative, b_negative⟩ => by
    apply Exists.intro (⟨-a, Integer.negate_positive_of_negative a_negative⟩, ⟨-b, Integer.negate_positive_of_negative b_negative⟩)
    simp [RationalEquivalent]
    rw [← Integer.negate_multiply_equal_multiply_negate, ← Integer.negate_multiply_equal_negate_multiply]

theorem less_than_of_subtract_positive {x y : ℚ} : 0 < y - x → x < y :=
  Quotient.inductionOn₂ x y <| by
  intro ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩
  intro ⟨(⟨u, u_positive⟩, ⟨v, v_positive⟩), (h : ((c * b + -a * d) * 1 + -0 * (d * b)) * v = u * (d * b * 1))⟩
  rw [Integer.multiply_one, ← Integer.negate_zero, Integer.zero_multiply, Integer.add_zero, Integer.multiply_one] at h
  apply Exists.intro (⟨u, u_positive⟩, ⟨v, v_positive⟩) h

theorem subtract_nonnegative_of_less_than {x y : ℚ} : x < y → 0 < y - x :=
  Quotient.inductionOn₂ x y <| by
  intro ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩
  intro ⟨(⟨u, u_positive⟩, ⟨v, v_positive⟩), (h : (c * b + -a * d) * v = u * (d * b))⟩
  apply Exists.intro (⟨u, u_positive⟩, ⟨v, v_positive⟩)
  have : Natural.fromNat 0 = (0 : ℤ) := rfl
  simp [Integer.multiply_one]
  rw [this, ← Integer.negate_zero, Integer.zero_multiply, Integer.add_zero]
  exact h

instance decidePositive (x : ℚ) : Decidable (0 < x) :=
  Quotient.recOnSubsingleton x
  λ ((a, ⟨b, b_nonzero⟩) : ℤ × Integer.NonZeroInteger) =>
  if h : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) then
    -- TODO: Figure out how to not have this
    let h' := by
      have : Natural.fromNat 0 = (0 : ℤ) := rfl
      rw [this, ← Integer.negate_zero, Integer.zero_multiply, Integer.multiply_one, Integer.add_zero]
      simp [Integer.multiply_one]
      exact h
    isTrue (equal_positive_of_positive_or_negative h')
  else
    let positive_or_negative_of_equal_positive' :
        (0 : ℚ) < Quotient.mk instanceSetoidRationalEquivalent (a, ⟨b, b_nonzero⟩) → (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
      simp [LessThan, subtract_zero, Quotient.lift_construct_on]
      intro ⟨(c, d), h⟩
      exact positive_or_negative_of_equal_positive h
    isFalse (mt positive_or_negative_of_equal_positive' h)

instance decideLessThan (x y : ℚ) : Decidable (x < y) :=
  if h : 0 < y - x then
    isTrue (less_than_of_subtract_positive h)
  else
    isFalse (mt subtract_nonnegative_of_less_than h)

theorem LessThan.connected : Relation.Connected LessThan := by
  unfold Relation.Connected
  apply Quotient.ind₂
  intro ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩
  intro h'
  -- TODO: Clean up
  have h : a * d ≠ c * b := by
    intro (h'' : ((a, ⟨b, b_nonzero⟩) : ℤ × NonZeroInteger) ≈ (c, ⟨d, d_nonzero⟩))
    exact absurd (Quotient.sound h'') h'
  have bd_nonzero := Integer.multiply_nonzero_of_nonzero b_nonzero d_nonzero
  match less_than_connected h, less_than_connected bd_nonzero with
  | Or.inl hadcb, Or.inl hbd =>
    have := Integer.subtract_negative_of_less_than hadcb
    rw [← Integer.subtract_definition, Integer.negate_multiply_equal_negate_multiply] at this
    exact Or.inr (equal_positive_of_positive_or_negative (Or.inr (And.intro this hbd)))
  | Or.inl hadcb, Or.inr hbd =>
    have := Integer.subtract_positive_of_less_than hadcb
    rw [← Integer.subtract_definition, Integer.negate_multiply_equal_negate_multiply] at this
    rw [Integer.multiply_commutative] at hbd
    exact Or.inl (equal_positive_of_positive_or_negative (Or.inl (And.intro this hbd)))
  | Or.inr hcbad, Or.inl hbd =>
    have := Integer.subtract_negative_of_less_than hcbad
    rw [← Integer.subtract_definition, Integer.negate_multiply_equal_negate_multiply] at this
    rw [Integer.multiply_commutative] at hbd
    exact Or.inl (equal_positive_of_positive_or_negative (Or.inr (And.intro this hbd)))
  | Or.inr hcbad, Or.inr hbd =>
    have this := Integer.subtract_positive_of_less_than hcbad
    rw [← Integer.subtract_definition, Integer.negate_multiply_equal_negate_multiply] at this
    exact Or.inr (equal_positive_of_positive_or_negative (Or.inl (And.intro this hbd)))

instance strictTotalOrder : DecidableStrictTotalOrder Rational where
  less_than_irreflexive := LessThan.irreflexive
  less_than_transitive := LessThan.transitive
  less_than_connected := LessThan.connected
  decideLessThan := decideLessThan
  decideEqual := decideEqual
  
instance totalOrder : DecidableTotalOrder Rational where
  decideLessEqual := λ _ _ => instDecidableOr

instance : LE Rational where
  le := totalOrderOfStrictTotalOrder.le

theorem add_left_less_than : ∀ {y z : ℚ} (x : ℚ), y < z → x + y < x + z := by
  apply Quotient.ind₃
  intro ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩ ⟨e, f, f_nonzero⟩
  intro ⟨(⟨u, u_positive⟩, ⟨v, v_positive⟩), (h : (c * b + -a * d) * v = u * (d * b))⟩
  apply Exists.intro (⟨u, u_positive⟩, ⟨v, v_positive⟩)
  show ((e*d + c*f)*(f*b) + -(e*b + a*f)*(f*d))*v = u*((f*d)*(f*b))
  -- TODO: Fix
  rw [Integer.right_distributive _ _ (f*b), Integer.negate_add, Integer.right_distributive _ _ (f*d), ← Integer.negate_multiply_equal_negate_multiply, Integer.multiply_associative e d _, Integer.multiply_commutative f b, Integer.multiply_left_commutative d _ _, Integer.multiply_commutative d f, ← Integer.multiply_associative e _ _, Integer.add_right_commutative, ← Integer.add_associative, Integer.add_inverse, Integer.zero_add, ← Integer.negate_multiply_equal_negate_multiply, Integer.multiply_associative, Integer.multiply_commutative f d, Integer.multiply_left_commutative f _ _, ← Integer.multiply_associative, Integer.negate_multiply_equal_negate_multiply, Integer.negate_multiply_equal_negate_multiply, Integer.multiply_associative c f _, Integer.multiply_left_commutative f b f, ← Integer.multiply_associative c _ _, ← Integer.right_distributive, Integer.multiply_right_commutative, Integer.add_commutative, Integer.multiply_associative d, Integer.multiply_left_commutative f b f, ← Integer.multiply_associative u, ← Integer.multiply_associative (u * d), Integer.multiply_associative u]
  exact congrArg (. * (f * f)) h

theorem add_right_less_than : ∀ {x y : ℚ} (z : ℚ), x < y → x + z < y + z := by
  intro x y z h
  rw [add_commutative x z, add_commutative y z]
  exact add_left_less_than z h

-- TODO
theorem multiply_less_than_of_positive_left : ∀ {x y z : ℚ}, y < z → 0 < x → x * y < x * z := by
  apply Quotient.ind₃
  intro ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩ ⟨e, f, f_nonzero⟩
  intro ⟨(⟨u, u_positive⟩, ⟨v, v_positive⟩), (hefcd : (e * d + -c * f) * v = u * (f * d))⟩
  intro ⟨(⟨s, s_positive⟩, ⟨t, t_positive⟩), (hab : (a*1 + -0*b)*t = s*(b*1))⟩
  rw [Integer.multiply_one, ← Integer.negate_zero, Integer.zero_multiply, Integer.add_zero, Integer.multiply_one] at hab
  apply Exists.intro (⟨u*s, Integer.multiply_positive u_positive s_positive⟩, ⟨v*t, Integer.multiply_positive v_positive t_positive⟩)
  show (a*e*(b*d) + -(a*c)*(b*f))*(v*t) = (u*s)*((b*f)*(b*d))
  rw [Integer.multiply_associative, Integer.multiply_left_commutative e, ← Integer.multiply_associative a, ← Integer.negate_multiply_equal_negate_multiply, Integer.multiply_associative a c, Integer.multiply_left_commutative c, ← Integer.multiply_associative a b, Integer.negate_multiply_equal_multiply_negate, ← Integer.left_distributive, Integer.multiply_commutative, Integer.multiply_commutative v t, Integer.multiply_left_commutative, Integer.multiply_associative t, ← Integer.multiply_associative, Integer.multiply_associative u s, ← Integer.multiply_associative s, ← Integer.multiply_associative s, ← hab, Integer.multiply_associative _ f, Integer.multiply_left_commutative f, ← Integer.multiply_associative _ b, Integer.multiply_left_commutative u, Integer.multiply_commutative v, Integer.negate_multiply_equal_negate_multiply, Integer.multiply_right_commutative a t]
  exact congrArg ((a * b * t) * .) hefcd

theorem multiply_less_than_of_positive_right : ∀ {x y z : ℚ}, x < y → 0 < z → x * z < y * z := by
  intro x y z hxy hz
  rw [multiply_commutative x z, multiply_commutative y z]
  exact multiply_less_than_of_positive_left hxy hz

-- TODO: Postpone defining ordered field until we have more algebra
-- TODO: Monotone definition
-- TODO: Associative, Commutative, Distributive definitions

def absolute (x : ℚ) : ℚ := maximum x (-x)

macro:max atomic("|" noWs) a:term noWs "|" : term => `(absolute $a)

/-
-- TODO: Gotta do some abstract algebra first, I'm not tryna do all those ordering proofs again
-- I'm officially stuck until I can clean some of this up.
--
theorem absolute_nonnegative (x : ℚ) : 0 ≤ |x| := by
  unfold absolute
  unfold maximum
  match less_than_trichotomous 0 x with
  | Or.inl h => sorry
  | Or.inr (Or.inl _) => sorry
  | Or.inr (Or.inr _) => sorry
  
theorem absolute_zero : |0| = 0 := rfl

theorem zero_of_absolute_value_zero (x : ℚ) : |x| = 0 → x = 0 := by
  skip
  
-- The triangle inequality
-- If only one of the terms is nonpositive, this decreases the absolute value, otherwise the two sides are equal
theorem absolute_add_less_equal (x y : ℚ) : |x + y| ≤ |x| + |y| := by
  skip
  
theorem absolute_less_equal_of_something (x y : ℚ) : -y ≤ x → x ≤ y → |x| ≤ y := by
  skip

theorem something_of_absolute_less_equal (x y : ℚ) : |x| ≤ y → -y ≤ x ∧ x ≤ y := by
  skip
  
theorem absolute_less_equal_equivalent_something (x y : ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  skip
  
theorem absolute_multiply_equal_multiply_absolute (x y : ℚ) : |x * y| = |x| * |y| := by
  skip
  
theorem absolute_negate (x : ℚ) : |-x| = |x| := by
  skip
-/

end Rational
