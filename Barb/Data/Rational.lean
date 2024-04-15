import Barb.Algebra
import Barb.Data.Integer
import Barb.Data.Option
import Barb.Logic

open Integer (NonZeroInteger)

def RationalEquivalent : (ℤ × NonZeroInteger) → (ℤ × NonZeroInteger) → Prop
  | (a, ⟨b, _⟩), (c, ⟨d, _⟩) => a * d = c * b

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

def LessEqual (x y : ℚ) : Prop := x < y ∨ x = y

instance : LE Rational where
  le := LessEqual

@[simp] theorem less_equal_definition : (x ≤ y) = (LessEqual x y) := rfl

theorem LessThan.irreflexive : Relation.Irreflexive LessThan := by
  intro x
  unfold LessThan
  simp
  rw [subtract_self, zero_definition, Quotient.lift_construct_on]
  intro ⟨(⟨a, a_positive⟩, ⟨b, _⟩), (hv : 0 * b = a * 1)⟩
  rw [Integer.zero_multiply, Integer.multiply_one] at hv
  exact absurd hv (not_equal_of_less_than a_positive)
  
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

theorem LessThan.asymmetric : Relation.Asymmetric LessThan := by
  unfold Relation.Asymmetric
  intro x y hxy hyx
  exact LessThan.irreflexive x (LessThan.transitive hxy hyx)
  
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
  | a, ⟨b, _⟩, Or.inl ⟨ha, hb⟩ =>
    Exists.intro (⟨a, ha⟩, ⟨b, hb⟩) (RationalEquivalent.reflexive _)
  | a, ⟨b, _⟩, Or.inr ⟨ha, hb⟩ => by
    apply Exists.intro (⟨-a, Integer.negate_strict_antitone ha⟩, ⟨-b, Integer.negate_strict_antitone hb⟩)
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

theorem LessEqual.reflexive : Relation.Reflexive LessEqual :=
  λ _ => Or.inr rfl
  
theorem LessEqual.antisymmetric : Relation.AntiSymmetric LessEqual :=
  λ hxy hyx =>
    match hxy, hyx with
    | Or.inl hxy, Or.inl hyx => False.elim (LessThan.asymmetric hxy hyx)
    | Or.inl _, Or.inr hyx => hyx.symm
    | Or.inr hxy, _ => hxy
  
theorem LessEqual.transitive : Relation.Transitive LessEqual :=
  λ hxy hyz =>
    match hxy, hyz with
    | Or.inl hxy, Or.inl hyz => Or.inl (LessThan.transitive hxy hyz)
    | Or.inl hxy, Or.inr hyz => Or.inl (hyz ▸ hxy)
    | Or.inr hxy, Or.inl hyz => Or.inl (hxy ▸ hyz)
    | Or.inr hxy, Or.inr hyz => Or.inr (hxy.trans hyz)

theorem LessEqual.strongly_connected : Relation.StronglyConnected LessEqual :=
  λ a b =>
    if h_equal : a = b then
      Or.inl (Or.inr h_equal)
    else
      match LessThan.connected h_equal with
      | Or.inl h_less => Or.inl (Or.inl h_less)
      | Or.inr h_greater => Or.inr (Or.inl h_greater)

instance totalOrder : DecidableTotalOrder Rational where
  less_equal_reflexive := LessEqual.reflexive
  less_equal_antisymmetric := LessEqual.antisymmetric
  less_equal_transitive := LessEqual.transitive
  less_equal_strongly_connected := LessEqual.strongly_connected
  decideEqual := decideEqual
  decideLessEqual := λ _ _ => instDecidableOr
  decideLessThan := decideLessThan
  lt := LessThan
  less_than_equivalent_less_equal_not_less_equal := by
    intro x y
    apply Iff.intro
    . intro hxy
      apply And.intro
      . exact Or.inl hxy
      . intro hyx
        match hyx with
        | Or.inl h_less => exact LessThan.asymmetric hxy h_less
        | Or.inr h_equal => exact absurd (h_equal ▸ hxy) (LessThan.irreflexive x)
    . intro h
      match h.left with
      | Or.inl h_less => exact h_less
      | Or.inr h_equal => exact False.elim (h.right (Or.inr h_equal.symm))

theorem add_left_strict_monotone : ∀ x : ℚ, StrictMonotone (x + .) := by
  apply Quotient.ind₃
  -- TODO: Rename the variables, this was left over from when it was different
  intro ⟨e, f, f_nonzero⟩ ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩ 
  intro ⟨(⟨u, u_positive⟩, ⟨v, v_positive⟩), (h : (c * b + -a * d) * v = u * (d * b))⟩
  apply Exists.intro (⟨u, u_positive⟩, ⟨v, v_positive⟩)
  show ((e*d + c*f)*(f*b) + -(e*b + a*f)*(f*d))*v = u*((f*d)*(f*b))
  -- TODO: Fix
  rw [Integer.right_distributive _ _ (f*b), Integer.negate_add, Integer.right_distributive _ _ (f*d), ← Integer.negate_multiply_equal_negate_multiply, Integer.multiply_associative e d _, Integer.multiply_commutative f b, Integer.multiply_left_commutative d _ _, Integer.multiply_commutative d f, ← Integer.multiply_associative e _ _, Integer.add_right_commutative, ← Integer.add_associative, Integer.add_inverse, Integer.zero_add, ← Integer.negate_multiply_equal_negate_multiply, Integer.multiply_associative, Integer.multiply_commutative f d, Integer.multiply_left_commutative f _ _, ← Integer.multiply_associative, Integer.negate_multiply_equal_negate_multiply, Integer.negate_multiply_equal_negate_multiply, Integer.multiply_associative c f _, Integer.multiply_left_commutative f b f, ← Integer.multiply_associative c _ _, ← Integer.right_distributive, Integer.multiply_right_commutative, Integer.add_commutative, Integer.multiply_associative d, Integer.multiply_left_commutative f b f, ← Integer.multiply_associative u, ← Integer.multiply_associative (u * d), Integer.multiply_associative u]
  exact congrArg (. * (f * f)) h

theorem add_right_strict_monotone : ∀ z : ℚ, StrictMonotone (. + z) := by
  intro z x y h
  simp
  rw [add_commutative x z, add_commutative y z]
  exact add_left_strict_monotone z h
  
theorem less_than_of_add_less_than_left {x y z : ℚ} (h : x + y < x + z) : y < z := by
  have := add_left_strict_monotone (-x) h
  simp [negate_add_cancel_left] at this
  exact this

theorem less_than_of_add_less_than_right {x y z : ℚ} (h : x + z < y + z) : x < y := by
  rw [add_commutative x z, add_commutative y z] at h
  exact less_than_of_add_less_than_left h
  
theorem add_less_than_add {w x y z : ℚ} (hwy : w < y) (hxz : x < z) : w + x < y + z :=
  less_than_transitive (add_right_strict_monotone x hwy) (add_left_strict_monotone y hxz)

theorem less_than_add_of_nonnegative_left {x y : ℚ} (h : 0 < y) : x < y + x := by
  have := add_right_strict_monotone x h
  simp [zero_add] at this
  exact this

theorem less_than_add_of_nonnegative_right {x y : ℚ} (h : 0 < y) : x < x + y := by
  rw [add_commutative x y]
  exact less_than_add_of_nonnegative_left h

theorem less_than_of_subtract_negative {x y : ℚ} (h : x - y < 0) : x < y := by
  have := add_right_strict_monotone y h
  simp at this
  rw [zero_add, ← subtract_definition, negate_add_cancel_right] at this
  exact this

theorem subtract_negative_of_less_than {x y : ℚ} (h : x < y) : x - y < 0 := by
  have := add_right_strict_monotone (-y) h
  simp [subtract_self] at this
  exact this

theorem negate_strict_antitone : StrictAntitone negate := by
  intro x y h
  have hx := add_left_strict_monotone (-y) h
  simp [add_inverse_left] at hx
  have hy := add_right_strict_monotone (-x) hx
  simp at hy
  rw [← subtract_definition, add_negate_cancel_right, zero_subtract] at hy
  exact hy

theorem less_than_of_negate_less_than_negate {x y : ℚ} (h : -y < -x) : x < y :=
  suffices - -x < - -y by simp at this; exact this
  negate_strict_antitone h

-- TODO
theorem multiply_positive_left_strict_monotone : ∀ {x: ℚ}, 0 < x → StrictMonotone (x * .) := by
  apply Quotient.ind
  intro ⟨a, b, b_nonzero⟩
  intro ⟨(⟨s, s_positive⟩, ⟨t, t_positive⟩), (hab : (a*1 + -0*b)*t = s*(b*1))⟩
  apply Quotient.ind₂
  intro ⟨c, d, d_nonzero⟩ ⟨e, f, f_nonzero⟩
  intro ⟨(⟨u, u_positive⟩, ⟨v, v_positive⟩), (hefcd : (e * d + -c * f) * v = u * (f * d))⟩
  rw [Integer.multiply_one, ← Integer.negate_zero, Integer.zero_multiply, Integer.add_zero, Integer.multiply_one] at hab
  apply Exists.intro (⟨u*s, Integer.multiply_positive u_positive s_positive⟩, ⟨v*t, Integer.multiply_positive v_positive t_positive⟩)
  show (a*e*(b*d) + -(a*c)*(b*f))*(v*t) = (u*s)*((b*f)*(b*d))
  rw [Integer.multiply_associative, Integer.multiply_left_commutative e, ← Integer.multiply_associative a, ← Integer.negate_multiply_equal_negate_multiply, Integer.multiply_associative a c, Integer.multiply_left_commutative c, ← Integer.multiply_associative a b, Integer.negate_multiply_equal_multiply_negate, ← Integer.left_distributive, Integer.multiply_commutative, Integer.multiply_commutative v t, Integer.multiply_left_commutative, Integer.multiply_associative t, ← Integer.multiply_associative, Integer.multiply_associative u s, ← Integer.multiply_associative s, ← Integer.multiply_associative s, ← hab, Integer.multiply_associative _ f, Integer.multiply_left_commutative f, ← Integer.multiply_associative _ b, Integer.multiply_left_commutative u, Integer.multiply_commutative v, Integer.negate_multiply_equal_negate_multiply, Integer.multiply_right_commutative a t]
  exact congrArg ((a * b * t) * .) hefcd

theorem multiply_positive_right_strict_monotone : ∀ {z : ℚ}, 0 < z → StrictMonotone (. * z) := by
  intro z hz x y hxy
  simp [multiply_commutative x z, multiply_commutative y z]
  exact multiply_positive_left_strict_monotone hz hxy

theorem multiply_positive {x y : ℚ} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  have := multiply_positive_left_strict_monotone hx hy
  simp [multiply_zero] at this
  exact this

theorem multiply_negative {x y : ℚ} (hx : x < 0) (hy : y < 0) : 0 < x * y := by
  have := multiply_positive_left_strict_monotone (negate_strict_antitone hx) (negate_strict_antitone hy)
  simp at this
  rw [← negate_zero, multiply_zero, ← negate_multiply_equal_negate_multiply, ← negate_multiply_equal_multiply_negate, negate_negate] at this
  exact this

theorem multiply_negative_of_positive_of_negative {x y : ℚ} (hx : 0 < x) (hy : y < 0) : x * y < 0 := by
  rw [← multiply_zero x]
  exact multiply_positive_left_strict_monotone hx hy

theorem multiply_negative_of_negative_of_positive {x y : ℚ} (hx : x < 0) (hy : 0 < y) : x * y < 0 := by
  rw [← zero_multiply y]
  exact multiply_positive_right_strict_monotone hy hx

theorem multiply_less_than_multiply {w x y z : ℚ} (hwy : w < y) (hxz : x < z) (hx : 0 < x) (hy : 0 < y) : w * x < y * z :=
  less_than_transitive
  (multiply_positive_right_strict_monotone hx hwy)
  (multiply_positive_left_strict_monotone hy hxz)

theorem multiply_negative_left_strict_antitone {x : ℚ} (hx : x < 0) : StrictAntitone (x * .) := by
  intro y z h
  have := multiply_positive_left_strict_monotone (negate_strict_antitone hx) h
  simp [← negate_multiply_equal_negate_multiply, ← negate_multiply_equal_negate_multiply] at this
  exact less_than_of_negate_less_than_negate this
  
theorem multiply_negative_right_strict_antitone {z : ℚ} (hz : z < 0) : StrictAntitone (. * z) := by
  intro x y h
  simp [multiply_commutative x z, multiply_commutative y z]
  exact multiply_negative_left_strict_antitone hz h

theorem add_left_monotone (x : ℚ) : Monotone (x + .) := by
  unfold Monotone
  intro y z h
  simp
  match h with
  | Or.inl h => exact Or.inl (add_left_strict_monotone x h)
  | Or.inr h => exact Or.inr (congrArg (x + .) h)

theorem add_right_monotone (z : ℚ) : Monotone (. + z) := by
  intro x y h
  simp
  rw [add_commutative x z, add_commutative y z]
  exact add_left_monotone z h

theorem less_equal_of_add_less_equal_left {x y z : ℚ} (h : x + y ≤ x + z) : y ≤ z := by
  have := add_left_monotone (-x) h
  simp [negate_add_cancel_left] at this
  exact this

theorem less_equal_of_add_less_equal_right {x y z : ℚ} (h : x + z ≤ y + z) : x ≤ y := by
  rw [add_commutative x z, add_commutative y z] at h
  exact less_equal_of_add_less_equal_left h

theorem add_less_equal_add {w x y z : ℚ} (hwy : w ≤ y) (hxz : x ≤ z) : w + x ≤ y + z :=
  less_equal_transitive (add_right_monotone x hwy) (add_left_monotone y hxz)

theorem less_equal_add_of_nonnegative_left {a b : ℚ} (h : 0 ≤ b) : a ≤ b + a := by
  have := add_less_equal_add h (less_equal_reflexive a)
  rw [zero_add] at this
  exact this

theorem less_equal_add_of_nonnegative_right {a b : ℚ} (h : 0 ≤ b) : a ≤ a + b := by
  rw [add_commutative a b]
  exact less_equal_add_of_nonnegative_left h
  
theorem less_equal_of_subtract_nonpositive {a b : ℚ} (h : a - b ≤ 0) : a ≤ b := by
  have := add_right_monotone b h
  simp [zero_add] at this
  rw [← subtract_definition, negate_add_cancel_right] at this
  exact this

theorem subtract_nonpositive_of_less_equal {a b : ℚ} (h : a ≤ b) : a - b ≤ 0 := by
  have := add_right_monotone (-b) h
  simp [subtract_self] at this
  exact this
  
theorem negate_antitone : Antitone negate := by
  intro a b h
  have ha := add_right_monotone (-a) h
  simp [add_inverse, add_commutative] at ha
  have hb := add_right_monotone (-b) ha
  simp at hb
  rw [subtract_self, zero_subtract, ← subtract_definition, ← subtract_definition, add_right_commutative, add_inverse, zero_add] at hb
  exact hb

theorem less_equal_of_negate_less_equal_negate {a b : ℚ} (h : -b ≤ -a) : a ≤ b :=
  suffices - -a ≤ - -b by simp at this; exact this
  negate_antitone h
  
theorem multiply_nonnegative_left_monotone {x : ℚ} (hx : 0 ≤ x) : Monotone (x * .) := by
  unfold Monotone
  intro y z h
  simp at h
  match h, hx with
  | Or.inl h, Or.inl hx => 
    exact Or.inl (multiply_positive_left_strict_monotone hx h)
  | Or.inl _, Or.inr hx => 
    apply less_equal_of_equal
    simp [← hx, zero_multiply]
  | Or.inr h, Or.inl _ =>
    apply less_equal_of_equal
    simp [h]
  | Or.inr _, Or.inr hx =>
    apply less_equal_of_equal
    simp [← hx, zero_multiply]
  
theorem multiply_nonnegative_right_monotone {c : ℚ} (hc : 0 ≤ c) : Monotone (. * c) := by
  unfold Monotone
  intro a b h
  simp
  rw [multiply_commutative a c, multiply_commutative b c]
  exact multiply_nonnegative_left_monotone hc h

theorem multiply_nonnegative {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have := multiply_nonnegative_left_monotone ha hb
  simp [multiply_zero] at this
  exact this
  
theorem multiply_nonpositive {a b : ℚ} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  have := multiply_nonnegative (negate_antitone ha) (negate_antitone hb)
  rw [negate_definition, negate_definition, ← negate_multiply_equal_multiply_negate, ← negate_multiply_equal_negate_multiply, negate_negate] at this
  exact this

theorem multiply_nonpositive_of_nonnegative_of_nonpositive {a b : ℚ} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  rw [← multiply_zero a]
  exact multiply_nonnegative_left_monotone ha hb

theorem multiply_nonpositive_of_nonpositive_of_nonnegative {a b : ℚ} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  rw [← zero_multiply b]
  exact multiply_nonnegative_right_monotone hb ha
  
-- Tricky: We only require that c is nonnegative, a is totally cool to be negative because that will make a*b negative which preserves order
theorem multiply_less_equal_multiply {a b c d : ℚ} (hac : a ≤ c) (hbd : b ≤ d) (hb : 0 ≤ b) (hc : 0 ≤ c) : a * b ≤ c * d :=
  less_equal_transitive
  (multiply_nonnegative_right_monotone hb hac)
  (multiply_nonnegative_left_monotone hc hbd)
  
theorem multiply_nonpositive_left_antitone {a : ℚ} (ha : a ≤ 0) : Antitone (a * .) := by
  intro b c h
  have := multiply_nonnegative_left_monotone (negate_antitone ha) h
  simp at this
  rw [← negate_multiply_equal_negate_multiply, ← negate_multiply_equal_negate_multiply] at this
  exact less_equal_of_negate_less_equal_negate this

theorem multiply_nonpositive_right_antitone {c : ℚ} (hc : c ≤ 0) : Antitone (. * c) := by
  intro a b h
  simp
  rw [multiply_commutative a c, multiply_commutative b c]
  exact multiply_nonpositive_left_antitone hc h

def NonNegativeRational := {x : ℚ // 0 ≤ x}
def PositiveRational := {x : ℚ // 0 < x}
def NonZero := {x : ℚ // x ≠ 0}
def NegativeRational := {x : ℚ // x < 0}
def NonPositiveRational := {x : ℚ // x ≤ 0}

def magnitude (x : ℚ) : ℚ := maximum x (-x)

macro:max atomic("|" noWs) a:term noWs "|" : term => `(magnitude $a)

theorem magnitude_negate (x : ℚ) : |-x| = |x| := by
  unfold magnitude 
  rw [negate_negate, maximum_commutative]

theorem magnitude_nonnegative (x : ℚ) : 0 ≤ |x| := by
  unfold magnitude
  match less_than_trichotomous 0 x with
  | Or.inl h => 
    exact less_equal_maximum_left_of_less_equal (-x) (less_equal_of_less_than h)
  | Or.inr (Or.inl h) =>
    rw [← h, ← negate_zero, maximum_self]
    exact less_equal_reflexive 0
  | Or.inr (Or.inr h) =>
    exact less_equal_maximum_right_of_less_equal x (negate_antitone (less_equal_of_less_than h))
  
theorem magnitude_zero : |0| = 0 := rfl

theorem zero_of_magnitude_value_zero {x : ℚ} (h : |x| = 0) : x = 0 := by
  rw [magnitude] at h
  match Decidable.em (x ≤ -x) with
  | Or.inl hx => 
    have := congrArg negate ((maximum_equal_right hx).symm.trans h)
    simp at this
    exact this
  | Or.inr hx => 
    exact (maximum_equal_left (greater_equal_of_not_less_equal hx)).symm.trans h

theorem magnitude_equal_of_nonnegative {x : ℚ} (h : 0 ≤ x) : |x| = x :=
  maximum_equal_left (less_equal_transitive (negate_antitone h) h)

theorem magnitude_equal_negate_of_nonpositive {x : ℚ} (h : x ≤ 0) : |x| = -x :=
  maximum_equal_right (less_equal_transitive h (negate_antitone h))
  
theorem magnitude_equal_of_positive (x : ℚ) : 0 < x → |x| = x :=
  magnitude_equal_of_nonnegative ∘ less_equal_of_less_than

theorem magnitude_equal_negate_of_negative (x : ℚ) : x < 0 → |x| = -x :=
  magnitude_equal_negate_of_nonpositive ∘ less_equal_of_less_than

theorem less_equal_magnitude (x : ℚ) : x ≤ |x| :=
  less_equal_maximum_left x (-x)

theorem negate_magnitude_less_equal (x : ℚ) : -|x| ≤ x := by
  have := negate_antitone (less_equal_magnitude (-x))
  simp [magnitude_negate] at this
  exact this
  
theorem magnitude_less_equal_equivalent_negate_less_equal_self {x y : ℚ} :
    -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  apply Iff.intro
  . intro h
    rw [magnitude]
    have := negate_antitone h.left
    simp at this
    exact maximum_less_equal h.right this
  . intro h
    rw [magnitude] at h
    have := negate_antitone (less_equal_right_of_maximum_less_equal h)
    simp at this
    exact And.intro this (less_equal_left_of_maximum_less_equal h)
  
theorem magnitude_less_equal_of_negate_less_equal {x y : ℚ} : -y ≤ x → x ≤ y → |x| ≤ y :=
  λ hyx hxy =>
  magnitude_less_equal_equivalent_negate_less_equal_self.mp (And.intro hyx hxy)

theorem negate_less_equal_of_magnitude_less_equal (x y : ℚ) : |x| ≤ y → -y ≤ x ∧ x ≤ y :=
  magnitude_less_equal_equivalent_negate_less_equal_self.mpr
  
theorem magnitude_multiply_equal_multiply_magnitude (x y : ℚ) : |x * y| = |x| * |y| := by
  match less_equal_strongly_connected 0 x, less_equal_strongly_connected 0 y with
  | Or.inl hx, Or.inl hy =>
    have := multiply_nonnegative hx hy
    rw [magnitude_equal_of_nonnegative this, magnitude_equal_of_nonnegative hx, 
      magnitude_equal_of_nonnegative hy]
  | Or.inl hx, Or.inr hy =>
    have := multiply_nonpositive_of_nonnegative_of_nonpositive hx hy
    rw [magnitude_equal_negate_of_nonpositive this, magnitude_equal_of_nonnegative hx, 
      magnitude_equal_negate_of_nonpositive hy, ← negate_multiply_equal_multiply_negate]
  | Or.inr hx, Or.inl hy =>
    have := multiply_nonpositive_of_nonnegative_of_nonpositive hy hx
    rw [multiply_commutative] at this
    rw [magnitude_equal_negate_of_nonpositive this, magnitude_equal_negate_of_nonpositive hx, 
      magnitude_equal_of_nonnegative hy, ← negate_multiply_equal_negate_multiply]
  | Or.inr hx, Or.inr hy =>
    have := multiply_nonpositive hx hy
    rw [magnitude_equal_of_nonnegative this, magnitude_equal_negate_of_nonpositive hx, 
      ← negate_multiply_equal_negate_multiply, magnitude_equal_negate_of_nonpositive hy, 
      ← negate_multiply_equal_multiply_negate, negate_negate]

-- The triangle inequality
-- If only one of the terms is nonpositive, this decreases the magnitude value, otherwise the two sides are equal
theorem magnitude_add_less_equal (x y : ℚ) : |x + y| ≤ |x| + |y| := by
  apply magnitude_less_equal_of_negate_less_equal
  . rw [negate_add]
    exact add_less_equal_add (negate_magnitude_less_equal x) (negate_magnitude_less_equal y)
  . exact add_less_equal_add (less_equal_magnitude x) (less_equal_magnitude y)

def distance (x y : ℚ) := |x - y|

theorem distance_nonnegative (x y : ℚ) : 0 ≤ distance x y := by
  exact magnitude_nonnegative (x - y)

theorem distance_self (x : ℚ) : distance x x = 0 := by
  unfold distance
  rw [subtract_self]
  exact magnitude_zero

theorem distance_zero_equivalent_equal {x y : ℚ} : distance x y = 0 ↔ x = y := by
  apply Iff.intro
  . intro h
    unfold distance magnitude at h
    match less_equal_strongly_connected (x - y) (-(x - y)) with
    | Or.inl hxy =>
      have := (maximum_equal_right hxy).symm.trans h
      simp [negate_subtract] at this
      exact (equal_of_subtract_equal_zero this).symm
    | Or.inr hxy =>
      have := (maximum_equal_left hxy).symm.trans h
      exact equal_of_subtract_equal_zero this
  . intro h
    subst h
    exact distance_self x

theorem equal_of_distance_zero {x y : ℚ} : distance x y = 0 → x = y :=
  distance_zero_equivalent_equal.mp

theorem distance_zero_of_equal {x y : ℚ} : x = y → distance x y = 0 :=
  distance_zero_equivalent_equal.mpr

theorem distance_commutative (x y : ℚ) : distance x y = distance y x := by
  unfold distance
  rw [← magnitude_negate, negate_subtract]

theorem distance_triangle (x y z : ℚ) : distance x z ≤ distance x y + distance y z := by
  unfold distance
  have := magnitude_add_less_equal (x - y) (y - z)
  rw [← subtract_definition, add_associative, ← subtract_definition, 
    negate_add_cancel_left] at this
  exact this

theorem distance_less_equal_reflexive {ε : ℚ} (hε : 0 < ε) : Relation.Reflexive (distance . . ≤ ε) := by
  skip

theorem equal_of_forall_distance_less_equal {x y : ℚ} : (∀ {ε}, 0 < ε → distance x y ≤ ε) → x = y := by
  skip

theorem distance_less_equal_symmetric {ε : ℚ} (hε : 0 < ε) : Relation.Symmetric (distance . . ≤ ε) := by
  skip

theorem distance_less_equal_transitive {ε δ x y : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    distance x y ≤ ε → distance y z ≤ δ → distance x z ≤ (ε + δ) := by
  skip

theorem distance_less_equal_add {ε δ w x y z : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    distance x y ≤ ε → distance z w ≤ δ → distance (x + z) (y + w) ≤ (ε + δ) := by
  skip

theorem distance_less_equal_subtract {ε δ w x y z : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    distance x y ≤ ε → distance z w ≤ δ → distance (x - z) (y - w) ≤ (ε + δ) := by
  skip

-- TODO: name
theorem distance_less_equal_of_less_than {ε ε' x y : ℚ} (hε : 0 < ε) (hε' : ε < ε') : distance x y ≤ ε → distance x y ≤ ε' := by
  skip

-- TODO: name
theorem distance_less_equal_between {ε w x y z: ℚ} (hε : 0 < ε) :
    distance x y ≤ ε → distance x z ≤ ε →
    (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y) →
    distance x w ≤ ε := by
  skip

theorem distance_less_equal_multiply_left {ε w x y : ℚ} (hε : 0 < ε) (hw : w ≠ 0) :
    distance x y ≤ ε → distance (w * x) (w * y) ≤ (|w| * ε) := by
  skip

theorem distance_less_equal_multiply_right {ε z x y : ℚ} (hε : 0 < ε) (hz : z ≠ 0) :
    distance x y ≤ ε → distance (x * z) (y * z) ≤ (ε * |z|) := by
  rw [multiply_commutative x z, multiply_commutative y z, multiply_commutative ε |z|]
  exact distance_less_equal_multiply_left hε hz

-- TODO: name
theorem distance_less_equal_multiply {ε δ w x y z : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    distance x y ≤ ε → distance z w ≤ δ →
    distance (x * z) (y * w) ≤ (ε * |z| + δ * |x| + ε * δ) := by
  skip
