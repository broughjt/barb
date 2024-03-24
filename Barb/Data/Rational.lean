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
  ofNat := ⟦(Integer.ofNatural (Natural.natToNatural n), ⟨1, by decide⟩)⟧

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

-- Here we appeal to asymmetry of less than on the integers. We suppose both x < y and y < x, lower these statements to statements about integer representatives for x and y, and then show that supposing both contradicts the asymmetry property of the less than relation for the integers.
theorem LessThan.Asymmetric : Relation.Asymmetric LessThan := by
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

end Rational
