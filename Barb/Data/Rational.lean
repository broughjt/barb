import Barb.Algebra
import Barb.Data.Integer
import Barb.Data.Option
import Barb.Logic
import Barb.Syntax

def RationalEquivalent : (ℤ × ℤ≠0) → (ℤ × ℤ≠0) → Prop
  | (a, ⟨b, _⟩), (c, ⟨d, _⟩) => a * d = c * b

theorem RationalEquivalent.reflexive : Reflexive RationalEquivalent :=
  λ _ => rfl

theorem RationalEquivalent.symmetric : Symmetric RationalEquivalent := by
  intro (a, ⟨b, _⟩) (c, ⟨d, _⟩) (h_ab_cd : a * d = c * b)
  exact h_ab_cd.symm

theorem RationalEquivalent.transitive : Transitive RationalEquivalent := by
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

instance instanceHasEquivRationalEquivalent : HasEquiv (Integer × ℤ≠0) where
  Equiv := RationalEquivalent

instance instanceSetoidRationalEquivalent : Setoid (Integer × ℤ≠0) where
  r := RationalEquivalent
  iseqv := RationalEquivalent.is_equivalence

@[simp] def RationalEquivalent.definition : (x ≈ y) = RationalEquivalent x y := rfl

instance decideRationalEquivalent (x y : ℤ × ℤ≠0) : Decidable (x ≈ y) :=
  let (a, ⟨b, _⟩) := x
  let (c, ⟨d, _⟩) := y
  Integer.decideEqual (a * d) (c * b)

instance decideRationalEquivalentQuotientEqual : DecidableEq (Quotient instanceSetoidRationalEquivalent) :=
  inferInstance

def Rational := Quotient instanceSetoidRationalEquivalent

namespace Rational

notation "ℚ" => Rational

instance decideEqual : DecidableEq Rational := decideRationalEquivalentQuotientEqual

def ofInteger (a : ℤ) : ℚ := ⟦(a, ⟨1, by decide⟩)⟧

def ofNatural : ℕ → ℚ := ofInteger ∘ Integer.ofNatural

instance : Coe Integer Rational := ⟨ofInteger⟩

instance : Coe Natural Rational := ⟨ofNatural⟩

instance : OfNat Rational n where
  ofNat := ofNatural (Natural.fromNat n)

instance zero : Rational := ofNatural 0

theorem zero_definition : (0 : ℚ) = Quotient.mk instanceSetoidRationalEquivalent (0, ⟨1, by decide⟩) := rfl

instance one : Rational := ofNatural 1

theorem one_definition : (1 : ℚ) = Quotient.mk instanceSetoidRationalEquivalent (1, ⟨1, by decide⟩) := rfl

def NonZeroRational := {x : ℚ // x ≠ 0}

notation "ℚ≠0" => NonZeroRational

def divideInteger (a : ℤ) (b : ℤ≠0) : ℚ := ⟦(a, b)⟧

infixl:70 " /. " => divideInteger

-- Need this for reducing boilerplate for integer exponentiation later
instance : Coe NonZeroRational Rational where
  coe x := x.val

def add : ℚ → ℚ → ℚ :=
  let add' := λ
  ((a, ⟨b, b_nonzero⟩) : ℤ × ℤ≠0)
  ((c, ⟨d, d_nonzero⟩) : ℤ × ℤ≠0) =>
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
  ((a, ⟨b, b_nonzero⟩) : ℤ × ℤ≠0)
  ((c, ⟨d, d_nonzero⟩) : ℤ × ℤ≠0) =>
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
  let negate' := λ ((a, ⟨b, b_nonzero⟩) : ℤ × ℤ≠0) => (-a, ⟨b, b_nonzero⟩)
  Quotient.map negate' <| by
  intro (a, ⟨b, b_nonzero⟩) (a', ⟨b', b'_nonzero⟩) (h : a*b' = a'*b)
  show (-a)*b' = (-a')*b
  rw [← Integer.negate_multiply_equal_negate_multiply, h, Integer.negate_multiply_equal_negate_multiply]

instance : Neg Rational where neg := negate

@[simp] theorem negate_definition : negate x = -x := rfl

theorem equal_zero_of_lift_numerator_equal_zero {a : ℤ} (b : ℤ≠0) :
    a = 0 → ⟦(a, b)⟧ = (0 : ℚ) := by
  intro h
  apply Quotient.sound
  show a * 1 = 0 * b
  simp [Integer.multiply_one, Integer.zero_multiply]
  exact h

theorem unlift_numerator_equal_zero_of_equal_zero {a : ℤ} {b : ℤ≠0} :
    ⟦(a, b)⟧ = (0 : ℚ) → a = 0 := by
  intro h
  have : a * 1 = 0 * b := Quotient.exact h
  rw [Integer.multiply_one, Integer.zero_multiply] at this
  exact this

def preReciprocal : ℤ × ℤ≠0 → Option ℚ≠0
  | (a, ⟨b, hb⟩) => 
  if ha : a ≠ 0 
  then some ⟨⟦(b, ⟨a, ha⟩)⟧, mt unlift_numerator_equal_zero_of_equal_zero hb⟩ 
  else none

@[simp]
theorem preReciprocal_none (x : ℤ × ℤ≠0) (h : x.1 = 0) : preReciprocal x = none := by
  simp [preReciprocal, h]

@[simp]
theorem preReciprocal_some (x : ℤ × ℤ≠0) (h : x.1 ≠ 0) :
    preReciprocal x = some ⟨⟦(x.2.val, ⟨x.1, h⟩)⟧, mt unlift_numerator_equal_zero_of_equal_zero x.2.property⟩ := by
  simp [preReciprocal, h]

def reciprocal' : ℚ → Option ℚ≠0 :=
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
    { simp [this, NonZeroRational]
      apply Quotient.sound
      show b * c = d * a
      simp [h, Integer.multiply_commutative] }
    apply And.left
    apply Integer.nonzero_of_multiply_nonzero
    intro hcb
    have := Integer.multiply_nonzero_of_nonzero ha hd
    exact absurd (hcb.symm.trans h.symm) this.symm

def reciprocal : ℚ≠0 → ℚ≠0 :=
  λ ⟨x, hx⟩ => Option.get (reciprocal' x) <| by
  have ⟨(a, ⟨b, hb⟩), hab⟩ := Quotient.exists_rep x
  have ha := mt (equal_zero_of_lift_numerator_equal_zero ⟨b, hb⟩) (hab.symm ▸ hx)
  rw [← hab, reciprocal', Quotient.lift_construct, Option.isSome]
  have := preReciprocal_some ⟨a, b, hb⟩ ha
  simp [this]

instance : Invert NonZeroRational where
  invert := reciprocal

@[simp]
theorem reciprocal_definition : reciprocal x = x⁻¹ := rfl

theorem add_associative : ∀ (x y z : ℚ), (x + y) + z = x + (y + z) := by
  apply Quotient.ind₃
  intro (a, ⟨b, _⟩) (c, ⟨d, _⟩) (e, ⟨f, _⟩)
  apply Quotient.sound
  show ((a*d + c*b)*f + e*(b*d))*(b*(d*f)) = (a*(d*f) + (c*f + e*d)*b)*((b*d)*f)
  let n_left := ((a*d + c*b)*f + e*(b*d)); let n_right := (a*(d*f) + (c*f + e*d)*b)
  let d_left := (b*(d*f)); let d_right := ((b*d)*f)
  suffices n_left = n_right ∧ d_left = d_right by 
  { show n_left * d_left = n_right * d_right
    simp [this.left, this.right] }
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

theorem multiply_inverse : ∀ (x : ℚ≠0), x.val * (x⁻¹).val = 1 := by
  intro ⟨x, hx⟩
  induction x using Quotient.inductionOn with
  | h p =>
    -- TODO: Why can't we just do this like | (a, ⟨b, hb⟩) =>
    let (a, ⟨b, hb⟩) := p
    have ha := mt (equal_zero_of_lift_numerator_equal_zero ⟨b, hb⟩) hx
    simp [← reciprocal_definition, reciprocal, reciprocal', preReciprocal_some (a, ⟨b, hb⟩) ha]
    apply Quotient.sound
    show (a * b) * 1 = 1 * (b * a)
    simp [Integer.multiply_commutative]

instance field : Field Rational where
  exists_pair_not_equal := ⟨0, 1, by decide⟩

  add_associative := add_associative
  add_commutative := add_commutative
  add_zero := add_zero
  add_inverse := add_inverse

  multiply_associative := multiply_associative
  multiply_commutative := multiply_commutative
  multiply_one := multiply_one

  left_distributive := left_distributive
  right_distributive := right_distributive

  multiply_inverse := multiply_inverse

def subtract (x y : ℚ) : ℚ := x + (-y)

instance : Sub Rational where sub := subtract

@[simp]
theorem subtract_definition (x y : ℚ) : x + (-y) = x - y := rfl

def divide (x : ℚ) (y : ℚ≠0) : ℚ := x * (reciprocal y).val

theorem negate_involutive : Function.Involutive negate := by
  apply Quotient.ind
  intro (a, ⟨b, b_nonzero⟩)
  apply Quotient.sound
  show (- - a)*b = a * b
  rw [Integer.negate_negate]

@[simp]
theorem negate_negate : ∀ x : ℚ, - -x = x := λ x => negate_involutive x

theorem negate_injective : Function.Injective negate := by
  unfold Function.Injective
  intro x y h
  have := congrArg negate h
  simp at this
  exact this

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

theorem equal_zero_of_multiply_equal_zero : ∀ {x y : ℚ}, x * y = 0 → x = 0 ∨ y = 0 := by
  apply Quotient.ind₂
  intro ⟨a, b, hb⟩ ⟨c, d, hd⟩
  intro h
  have h' : (a * c) * 1 = 0 * (b * d) := Quotient.exact h
  rw [Integer.multiply_one, Integer.zero_multiply] at h'
  match Integer.equal_zero_of_multiply_equal_zero h' with
  | Or.inl ha =>
    apply Or.inl
    subst ha
    apply Quotient.sound
    show 0 * 1 = 0 * b
    simp [Integer.zero_multiply]
  | Or.inr hb =>
    apply Or.inr
    subst hb
    apply Quotient.sound
    show 0 * 1 = 0 * d
    simp [Integer.zero_multiply]

theorem multiply_equal_zero_of_equal_zero : ∀ {a b : ℚ}, a = 0 ∨ b = 0 → a * b = 0 := by
  intro a b h
  match h with
  | Or.inl ha => rw [ha, zero_multiply]
  | Or.inr hb => rw [hb, multiply_zero]

theorem multiply_left_commutative (n m k : ℚ) : n * (m * k) = m * (n * k) := by
  rw [← multiply_associative, multiply_commutative n m, multiply_associative]

theorem multiply_right_commutative (n m k : ℚ) : (n * m) * k = (n * k) * m := by
  rw [multiply_associative, multiply_commutative m k, ← multiply_associative]

theorem multiply_left_cancel {a b c : ℚ} (h : a * b = a * c) (a_nonzero : a ≠ 0) : b = c := by
  suffices c - b = 0 from (equal_of_subtract_equal_zero this).symm
  apply (Or.resolve_left . a_nonzero)
  apply equal_zero_of_multiply_equal_zero
  rw [← subtract_definition, left_distributive, ← h,
    ← negate_multiply_equal_multiply_negate, add_inverse]

theorem multiply_right_cancel {a b c : ℚ} (h : a * c = b * c) (c_nonzero : c ≠ 0) : a = b := by
  apply multiply_left_cancel (a := c)
  rw [multiply_commutative c a, multiply_commutative c b]
  exact h
  exact c_nonzero

theorem multiply_nonzero_of_nonzero {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  apply hb
  apply (multiply_left_cancel (a := a) . ha)
  rw [h, multiply_zero]

-- Field lemmas

theorem reciprocal_one : ((⟨1, by decide⟩ : ℚ≠0)⁻¹ : ℚ≠0) = (⟨1, by decide⟩ : ℚ≠0) := rfl
-- TODO: Figure out how to get the type checker to like RHS

theorem multiply_reciprocal (a b : ℚ≠0) : 
    let hab := multiply_nonzero_of_nonzero a.property b.property
    (⟨a.val * b.val, hab⟩⁻¹ : ℚ≠0).val = b⁻¹.val * a⁻¹.val := by
  let hab := multiply_nonzero_of_nonzero a.property b.property
  have := congrArg ((b⁻¹).val * (a⁻¹).val * .) (multiply_inverse ⟨a * b, hab⟩)
  simp at this
  rw [multiply_one, ← multiply_associative, multiply_associative (b⁻¹).val, ← multiply_associative (a⁻¹).val, multiply_commutative (a⁻¹).val, multiply_inverse, one_multiply, multiply_commutative (b⁻¹).val, multiply_inverse, one_multiply] at this
  exact this

theorem reciprocal_involutive (a : ℚ≠0) : a⁻¹⁻¹ = a := by
  let ⟨a', ha⟩ := a
  have := congrArg (a' * .) (multiply_inverse ⟨a', ha⟩⁻¹)
  simp at this
  rw [multiply_one, ← multiply_associative, multiply_inverse ⟨a', ha⟩, one_multiply] at this
  exact Subtype.eq this

theorem reciprocal_of_multiply_equal_one_left {x y : ℚ≠0} : x.val * y.val = 1 → y = x⁻¹ := by
  intro h
  have := congrArg (x⁻¹.val * .) h
  simp [← multiply_associative, multiply_commutative _ x.val, multiply_inverse, one_multiply, multiply_one] at this
  exact Subtype.eq this

theorem reciprocal_of_multiply_equal_one_right {x y : ℚ≠0} : x.val * y.val = 1 → x = y⁻¹ := by
  intro h
  have := congrArg (. * y⁻¹.val) h
  simp [multiply_associative, multiply_inverse, multiply_one, one_multiply] at this
  exact Subtype.eq this

theorem negate_reciprocal : ∀ {x : ℚ} (hx : x ≠ 0),
    let x' : ℚ≠0 := ⟨x, hx⟩
    let x'' : ℚ≠0 := ⟨-x, mt (@negate_injective x 0) hx⟩;
    -((x' : ℚ≠0)⁻¹).val = x''⁻¹.val := by
  apply Quotient.ind
  intro ⟨a, b, hb⟩
  intro hab1'
  have ha : a ≠ 0 := mt (equal_zero_of_lift_numerator_equal_zero ⟨b, hb⟩) hab1'
  simp [← reciprocal_definition, reciprocal, reciprocal', preReciprocal_some ⟨a, b, hb⟩ ha]
  have ha' : -a ≠ 0 := mt (@Integer.negate_injective a 0) ha
  simp [← negate_definition, negate, Quotient.map, Quot.map]
  conv => rhs; arg 1; arg 1; arg 3; rw [← Quotient.mk]
  simp [preReciprocal_some ⟨-a, b, hb⟩ ha']
  apply Quot.sound
  show (-b)*(-a) = b*a
  simp [← Integer.negate_multiply_equal_multiply_negate, ← Integer.negate_multiply_equal_negate_multiply]

theorem nonzero_of_multiply_nonzero {a b : ℚ} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  not_or.mp (mt multiply_equal_zero_of_equal_zero h)

theorem ofInteger_add (a b : ℤ) : ofInteger (a + b) = ofInteger a + ofInteger b := by
  apply Quotient.sound
  simp [Integer.multiply_one]
  rfl

theorem ofInteger_multiply (a b : ℤ) : ofInteger (a * b) = ofInteger a * ofInteger b := by
  apply Quotient.sound
  rfl

theorem ofInteger_injective : Function.Injective ofInteger := by
  intro a b h
  have : a * 1 = b * 1 := Quotient.exact h
  simp [Integer.multiply_one, Integer.one_multiply] at this
  exact this

theorem ofNatural_add (n m : ℕ) : ofNatural (n + m) = ofNatural n + ofNatural m := by
  apply Quotient.sound
  simp [Integer.multiply_one]
  rfl

theorem ofNatural_multiply (n m : ℕ) : ofNatural (n * m) = ofNatural n * ofNatural m := by
  apply Quotient.sound
  show Integer.ofNatural (n * m) * 1 = (Integer.ofNatural n * Integer.ofNatural m) * 1
  simp [Integer.multiply_one]
  exact Integer.ofNatural_multiply n m

theorem ofNatural_injective : Function.Injective ofNatural := by
  intro n m h
  have : Integer.ofNatural n * 1 = Integer.ofNatural m * 1 := Quotient.exact h
  simp [Integer.multiply_one] at this
  exact Integer.ofNatural_injective this

def LessThan (x y : ℚ) : Prop :=
  let positive'
    | (a, ⟨b, b_nonzero⟩) => ∃ v : Integer.PositiveInteger × Integer.PositiveInteger,
      let (⟨c, _⟩, ⟨d, d_positive⟩) := v;
      RationalEquivalent (a, ⟨b, b_nonzero⟩) (c, ⟨d, (not_equal_of_less_than d_positive).symm⟩)
  Quotient.liftOn (y - x) positive' <| by
  intro a b (h : a ≈ b)
  apply propext
  apply Iff.intro
  . intro ⟨v, hv⟩
    apply Exists.intro v (h.symmetric.transitive hv)
  . intro ⟨v, hv⟩
    apply Exists.intro v (h.transitive hv)

instance : LT Rational where
  lt := LessThan

theorem less_than_definition : (x < y) = (LessThan x y) := rfl

def LessEqual (x y : ℚ) : Prop := x < y ∨ x = y

instance : LE Rational where
  le := LessEqual

theorem less_equal_definition : (x ≤ y) = (LessEqual x y) := rfl

theorem LessThan.irreflexive : Irreflexive LessThan := by
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
theorem LessThan.transitive : Transitive LessThan := by
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

theorem LessThan.asymmetric : Asymmetric LessThan := by
  unfold Asymmetric
  intro x y hxy hyx
  exact LessThan.irreflexive x (LessThan.transitive hxy hyx)
  
theorem positive_or_negative_of_equal_positive : ∀ {a : ℤ} {b : ℤ≠0} {c d : Integer.PositiveInteger}, 
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

theorem equal_positive_of_positive_or_negative : ∀ {a : ℤ} {b : ℤ≠0},
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

theorem subtract_positive_of_less_than {x y : ℚ} : x < y → 0 < y - x :=
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
  λ ((a, ⟨b, b_nonzero⟩) : ℤ × ℤ≠0) =>
  if h : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) then
    -- -- TODO: Figure out how to not have this
    let h' := by
      have : Natural.fromNat 0 = (0 : ℤ) := rfl
      rw [this, ← Integer.negate_zero, Integer.zero_multiply, Integer.multiply_one, Integer.add_zero]
      simp [Integer.multiply_one]
      exact h
    isTrue (equal_positive_of_positive_or_negative h')
  else
    let positive_or_negative_of_equal_positive' :
        (0 : ℚ) < Quotient.mk instanceSetoidRationalEquivalent (a, ⟨b, b_nonzero⟩) → (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
      simp [less_than_definition, LessThan, subtract_zero, Quotient.lift_construct_on]
      intro (c, d) h
      exact positive_or_negative_of_equal_positive h
    isFalse (mt positive_or_negative_of_equal_positive' h)

instance decideLessThan (x y : ℚ) : Decidable (x < y) :=
  if h : 0 < y - x then
    isTrue (less_than_of_subtract_positive h)
  else
    isFalse (mt subtract_positive_of_less_than h)

theorem LessThan.connected : Connected LessThan := by
  unfold Connected
  apply Quotient.ind₂
  intro ⟨a, b, b_nonzero⟩ ⟨c, d, d_nonzero⟩
  intro h'
  -- TODO: Clean up
  have h : a * d ≠ c * b := by
    intro (h'' : ((a, ⟨b, b_nonzero⟩) : ℤ × ℤ≠0) ≈ (c, ⟨d, d_nonzero⟩))
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

theorem LessEqual.reflexive : Reflexive LessEqual :=
  λ _ => Or.inr rfl
  
theorem LessEqual.antisymmetric : AntiSymmetric LessEqual :=
  λ hxy hyx =>
    match hxy, hyx with
    | Or.inl hxy, Or.inl hyx => False.elim (LessThan.asymmetric hxy hyx)
    | Or.inl _, Or.inr hyx => hyx.symm
    | Or.inr hxy, _ => hxy
  
theorem LessEqual.transitive : Transitive LessEqual :=
  λ hxy hyz =>
    match hxy, hyz with
    | Or.inl hxy, Or.inl hyz => Or.inl (LessThan.transitive hxy hyz)
    | Or.inl hxy, Or.inr hyz => Or.inl (hyz ▸ hxy)
    | Or.inr hxy, Or.inl hyz => Or.inl (hxy ▸ hyz)
    | Or.inr hxy, Or.inr hyz => Or.inr (hxy.trans hyz)

theorem LessEqual.strongly_connected : StronglyConnected LessEqual :=
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
  unfold StrictMonotone
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
  -- TODO
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

theorem less_equal_of_subtract_nonnegative {a b : ℚ} (h : 0 ≤ b - a) : a ≤ b := by
  have := add_right_monotone a h
  simp at this
  rw [zero_add, ← subtract_definition, negate_add_cancel_right] at this
  exact this

theorem subtract_nonnegative_of_less_equal {a b : ℚ} (h : a ≤ b) : 0 ≤ b - a := by
  have := add_right_monotone (-a) h
  simp [subtract_self] at this
  exact this

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
-- See note on equal_of_forall_distance_less_equal
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

theorem reciprocal_positive_strict_antitone : ∀ {x y : ℚ} (hx : 0 < x) (hxy : x < y),
    let x' : ℚ≠0 := ⟨x, Ne.symm <| not_equal_of_less_than hx⟩
    let y' : ℚ≠0 := ⟨y, Ne.symm <| not_equal_of_less_than <| hx.transitive hxy⟩
    y'⁻¹.val < x'⁻¹.val := by
  -- Introduce extra implied assumptions explicitly to make quotient induction easier
  suffices h : ∀ (x y : ℚ) (hx : 0 < x) (_ : 0 < y) (_ : x ≠ 0) (_ : y ≠ 0) (_ : x ≠ y) (hxylt : x < y),
    let x' : ℚ≠0 := ⟨x, Ne.symm <| not_equal_of_less_than hx⟩
    let y' : ℚ≠0 := ⟨y, Ne.symm <| not_equal_of_less_than <| hx.transitive hxylt⟩
    y'⁻¹.val < x'⁻¹.val 
  by 
  { intro x y hx hxy
    let hy : 0 < y := hx.transitive hxy
    exact h x y hx hy (not_equal_of_less_than hx).symm (not_equal_of_less_than hy).symm (not_equal_of_less_than hxy) hxy
    }
  apply Quotient.ind₂
  intro ⟨a, b, hb⟩ ⟨c, d, hd⟩
  -- hx : 0 < x
  intro ⟨(⟨a1, ha1⟩, ⟨b1, hb1⟩), (ha1b1 : (a*1 + (-0)*b)*b1 = a1*(b*1))⟩
  simp [Integer.multiply_one, ← Integer.negate_zero, Integer.zero_multiply, Integer.add_zero] at ha1b1
  -- hy : 0 < y
  intro ⟨(⟨c1, hc1⟩, ⟨d1, hd1⟩), (hc1d1 : (c*1 + (-0)*d)*d1 = c1*(d*1))⟩
  simp [Integer.multiply_one, ← Integer.negate_zero, Integer.zero_multiply, Integer.add_zero] at hc1d1
  -- hx0 : x ≠ 0
  intro hab1'
  have ha : a ≠ 0 := mt (equal_zero_of_lift_numerator_equal_zero ⟨b, hb⟩) hab1'
  -- hy0 : y ≠ 0
  intro hcd1'
  have hc : c ≠ 0 := mt (equal_zero_of_lift_numerator_equal_zero ⟨d, hd⟩) hcd1'
  -- hxyne : x ≠ y
  intro habcd1'
  have habcd1 := mt Quotient.sound habcd1'
  simp [RationalEquivalent] at habcd1
  -- hxylt : x < y
  -- ∃ u,v>0, c/d - a/b = u/v
  intro ⟨(⟨u, hu⟩, ⟨v, hv⟩), (huv : (c*b + (-a)*d)*v = u*(d*b))⟩
  rw [← Integer.negate_multiply_equal_negate_multiply, Integer.subtract_definition] at huv
  simp [← reciprocal_definition, reciprocal, reciprocal', preReciprocal_some ⟨a, b, hb⟩ ha, preReciprocal_some ⟨c, d, hd⟩ hc]
  -- have 
  -- (c*b - a*d)*v = u*(d*b)
  -- a*b1 = a1*b 
  -- c*d1 = c1*d 
  -- gives (a1*c1)*b*d = a*c*(b1*d1)
  -- gives (c*b - a*d)*v*(a1*c1) = (u*a1*c1)*b*d = a*c*(u*b1*d1)
  have ha1c1bd : (a1*c1)*(b*d) = (a*c)*(b1*d1) := by
    rw [← Integer.multiply_associative (a1*c1) b d, Integer.multiply_right_commutative a1 c1 b, ← ha1b1, Integer.multiply_associative, ← hc1d1, Integer.multiply_associative, Integer.multiply_left_commutative b1, ← Integer.multiply_associative]
  have hub1d1ac : (u*a1*c1)*(b*d) = (u*b1*d1)*(a*c) := by
    rw [Integer.multiply_associative u, Integer.multiply_associative u, Integer.multiply_associative u, Integer.multiply_associative u, Integer.multiply_commutative (b1*d1)]
    exact congrArg (u * .) ha1c1bd
  have hua1c1bd : (b*c + (-d)*a)*(v*a1*c1) = (u*a1*c1)*(b*d) := by
    rw [Integer.multiply_commutative b c, ← Integer.negate_multiply_equal_negate_multiply, Integer.subtract_definition, Integer.multiply_commutative d a]
    rw [Integer.multiply_associative v, ← Integer.multiply_associative _ v]
    rw [Integer.multiply_associative u, Integer.multiply_commutative u, Integer.multiply_associative (a1 * c1), Integer.multiply_commutative (a1 * c1), Integer.multiply_commutative b d]
    exact congrArg (. * (a1 * c1)) huv
  have hva1c1 : 0 < v*a1*c1 := by
    rw [Integer.multiply_associative]
    exact Integer.multiply_positive hv (Integer.multiply_positive ha1 hc1)
  have hub1d1 : 0 < u*b1*d1 := by
    rw [Integer.multiply_associative]
    exact Integer.multiply_positive hu (Integer.multiply_positive hb1 hd1)
  exact Exists.intro (⟨u*b1*d1, hub1d1⟩, ⟨v*a1*c1, hva1c1⟩) (hua1c1bd.trans hub1d1ac)

-- TODO: reciprocal_negative
theorem reciprocal_positive_antitone : ∀ {x y : ℚ} (hx : 0 < x) (hxy : x ≤ y),
    let x' : ℚ≠0 := ⟨x, Ne.symm <| not_equal_of_less_than hx⟩
    let y' : ℚ≠0 := ⟨y, Ne.symm <| not_equal_of_less_than <| less_than_of_less_than_of_less_equal hx hxy⟩
    y'⁻¹.val ≤ x'⁻¹.val
  | x, y, hx, hxy =>
  match less_equal_equivalent_less_than_or_equal.mp hxy with
  | Or.inl hxy' => less_equal_of_less_than <| reciprocal_positive_strict_antitone hx hxy'
  | Or.inr hxy' => by simp [hxy', less_equal_of_equal]

theorem reciprocal_positive {x : ℚ} (hx : 0 < x) : 
    let x' : ℚ≠0 := ⟨x, Ne.symm <| not_equal_of_less_than hx⟩
    0 < x'⁻¹.val := by
  suffices ∀ (x : ℚ) (h1 : x ≠ 0) (_ : 0 < x),
    let x' : ℚ≠0 := ⟨x, h1⟩
    0 < x'⁻¹.val from this x (Ne.symm <| not_equal_of_less_than hx) hx
  apply Quotient.ind
  intro ⟨a, b, hb⟩ 
  intro (ha' : _)
  have ha : a ≠ 0 := mt (equal_zero_of_lift_numerator_equal_zero ⟨b, hb⟩) ha'
  intro ⟨(⟨u, hu⟩, ⟨v, hv⟩), (huv : (a*1 + (-0)*b)*v = u*(b*1))⟩
  simp [Integer.multiply_one, ← Integer.negate_zero, Integer.zero_multiply, Integer.add_zero] at huv
  simp [← reciprocal_definition, reciprocal, reciprocal', preReciprocal_some ⟨a, b, hb⟩ ha]
  exists (⟨v, hv⟩, ⟨u, hu⟩)
  show (b*1 + (-0)*a)*u = v*(a*1)
  simp [Integer.multiply_one, ← Integer.negate_zero, Integer.zero_multiply, Integer.add_zero]
  simp [Integer.multiply_commutative, huv]

theorem reciprocal_negative {x : ℚ} (hx : x < 0) : 
    let x' : ℚ≠0 := ⟨x, not_equal_of_less_than hx⟩
    x'⁻¹.val < 0 := by
  have h1 := negate_strict_antitone hx
  simp [← negate_zero] at h1
  have h2 := reciprocal_positive h1
  simp at h2
  have h3 := negate_reciprocal (not_equal_of_less_than hx)
  simp [← h3] at h2
  have h4 := negate_strict_antitone h2
  simp at h4
  exact h4

/-
theorem ofInteger_monotone : Monotone ofInteger := sorry

theorem ofInteger_strict_monotone : StrictMonotone ofInteger := sorry
-/

abbrev NonNegativeRational := {x : ℚ // 0 ≤ x}
abbrev PositiveRational := {x : ℚ // 0 < x}
abbrev NegativeRational := {x : ℚ // x < 0}
abbrev NonPositiveRational := {x : ℚ // x ≤ 0}

notation "ℚ≥0" => NonNegativeRational
notation "ℚ>0" => PositiveRational
notation "ℚ<0" => NegativeRational
notation "ℚ≤0" => NonPositiveRational

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
  
theorem magnitude_zero : |(0 : ℚ)| = 0 := rfl

theorem zero_of_magnitude_zero {x : ℚ} (h : |x| = 0) : x = 0 := by
  rw [magnitude] at h
  match Decidable.em (x ≤ -x) with
  | Or.inl hx => 
    have := congrArg negate ((maximum_equal_right hx).symm.trans h)
    simp at this
    exact this
  | Or.inr hx => 
    exact (maximum_equal_left (greater_equal_of_not_less_equal hx)).symm.trans h

theorem magnitude_positive {x : ℚ} (h : x ≠ 0) : 0 < |x| :=
  match less_than_or_equal_of_less_equal (magnitude_nonnegative x) with
  | Or.inl hx => hx
  | Or.inr hx => absurd hx.symm (mt zero_of_magnitude_zero h)

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

theorem negate_less_equal_of_magnitude_less_equal {x y : ℚ} : |x| ≤ y → -y ≤ x ∧ x ≤ y :=
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

theorem magnitude_reciprocal (x : ℚ≠0) :
    let x' : ℚ≠0 := ⟨|x.val|, Ne.symm <| not_equal_of_less_than <| magnitude_positive x.property⟩
    |x⁻¹.val| = x'⁻¹ := by
  match less_than_connected x.property with
  | Or.inl (hx : x.val < 0) =>
    have := reciprocal_negative hx
    simp [magnitude_equal_negate_of_negative x.val hx, magnitude_equal_negate_of_negative x⁻¹.val (reciprocal_negative hx)]
    rw [← negate_reciprocal (not_equal_of_less_than hx), Subtype.eta]
  | Or.inr (hx : 0 < x.val) =>
    simp [magnitude_equal_of_positive x.val hx, magnitude_equal_of_positive x⁻¹.val (reciprocal_positive hx), Subtype.eta]

def distance (x y : ℚ) := |x - y|

theorem distance_definition : distance x y = |x - y| := rfl

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

theorem distance_triangle (x z y : ℚ) : distance x z ≤ distance x y + distance y z := by
  unfold distance
  have := magnitude_add_less_equal (x - y) (y - z)
  rw [← subtract_definition, add_associative, ← subtract_definition, 
    negate_add_cancel_left] at this
  exact this

theorem distance_less_equal_reflexive {ε : ℚ} (hε : 0 < ε) : Reflexive (distance . . ≤ ε) := by
  intro x
  rw [distance_self x]
  exact less_equal_of_less_than hε

/-
Thought that I was going to have to develop several lemmas for multiplication 
by 1/2 or 1 preserving the inequalilty, but multiply_less_*_multiply covers all cases!
-/
theorem equal_of_forall_distance_less_equal {x y : ℚ} : (∀ {ε}, 0 < ε → distance x y ≤ ε) → x = y := by
  intro h
  suffices ∀ {x y}, ¬(x < y ∧ (∀ {ε}, 0 < ε → distance x y ≤ ε)) from
  match less_than_trichotomous x y with
  | Or.inl hxy => False.elim (this (And.intro hxy h))
  | Or.inr (Or.inl hxy) => hxy
  | Or.inr (Or.inr hxy) => by
    rw [distance_commutative x y] at h
    exact False.elim (this (And.intro hxy h))
  intro x y
  intro ⟨hxy, h⟩
  have hdxy := magnitude_positive <| Ne.symm <| not_equal_of_less_than 
            <| subtract_positive_of_less_than hxy
  apply absurd
  . have := multiply_positive_left_strict_monotone (by decide : 0 < 1 /. ⟨2, by decide⟩) hdxy
    simp only [multiply_zero] at this
    have := h this
    rw [distance_commutative, distance] at this
    exact this
  . have := less_than_of_less_equal_of_less_than
      (multiply_nonnegative_left_monotone (by decide : 0 ≤ 1 /. ⟨2, by decide⟩) (less_equal_reflexive |y - x|))
      (multiply_positive_right_strict_monotone hdxy (by decide : 1 /. ⟨2, by decide⟩ < 1))
    simp only [one_multiply] at this
    exact not_less_equal_of_greater_than this

theorem distance_less_equal_symmetric {ε : ℚ} (_ : 0 < ε) : Symmetric (distance . . ≤ ε) := by
  intro x y h
  rw [distance_commutative] at h
  exact h

theorem distance_less_equal_transitive {ε δ x y : ℚ} (_ : 0 < ε) (_ : 0 < δ) :
    distance x y ≤ ε → distance y z ≤ δ → distance x z ≤ (ε + δ)
  | hxy, hyz => less_equal_transitive (distance_triangle x z y) (add_less_equal_add hxy hyz)

theorem distance_less_equal_add {ε δ w x y z : ℚ} (_ : 0 < ε) (_ : 0 < δ) :
    distance x y ≤ ε → distance z w ≤ δ → distance (x + z) (y + w) ≤ (ε + δ) := by
  intro hxy hzw
  have := distance_triangle (x + z) (y + w) (y + z)
  unfold distance at this
  rw [← subtract_definition _ (y + z), negate_add, add_left_commutative, add_negate_cancel_right, ← subtract_definition (y + z) (y + w), negate_add, add_right_commutative, add_negate_cancel_left, ← distance, add_commutative (-y) _, add_commutative (-w) _, subtract_definition, ← distance, subtract_definition, ← distance] at this
  exact less_equal_transitive this (add_less_equal_add hxy hzw)

theorem distance_less_equal_subtract {ε δ w x y z : ℚ} (_ : 0 < ε) (_ : 0 < δ) :
    distance x y ≤ ε → distance z w ≤ δ → distance (x - z) (y - w) ≤ (ε + δ) := by
  intro hxy hzw
  have := distance_triangle (x - z) (y - w) (y - z)
  unfold distance at this
  rw [subtract_subtract x z (y - z), ← subtract_definition y z, add_left_commutative, add_inverse, add_zero, ← subtract_definition (y + (-z)) (y - w), negate_subtract, add_right_commutative, ← subtract_definition w y, add_left_commutative, add_inverse, add_zero, subtract_definition, ← distance, ← distance, ← distance, distance_commutative w z] at this
  exact less_equal_transitive this (add_less_equal_add hxy hzw)

-- TODO: name
-- TODO: corallary, also weaker than it could be since <
theorem distance_less_equal_of_less_than {ε ε' x y : ℚ} (_ : 0 < ε) (hε' : ε < ε') : distance x y ≤ ε → distance x y ≤ ε' :=
  λ h => less_equal_of_less_than <| less_than_of_less_equal_of_less_than h hε'

theorem distance_less_equal_between' {ε w x y z: ℚ} (_ : 0 < ε) :
    distance x y ≤ ε → distance x z ≤ ε →
    y ≤ w → w ≤ z →
    distance x w ≤ ε := by
  intro hxy hxz hyw hwz
  apply magnitude_less_equal_of_negate_less_equal
  . apply less_equal_transitive
    exact And.left <| negate_less_equal_of_magnitude_less_equal hxz
    exact add_left_monotone x <| negate_antitone hwz
  . apply less_equal_transitive
    exact add_left_monotone x <| negate_antitone hyw
    exact And.right <| negate_less_equal_of_magnitude_less_equal hxy

/-
theorem distance_less_equal_between {ε w x y z: ℚ} (hε : 0 < ε) :
    distance x y ≤ ε → distance x z ≤ ε →
    (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y) →
    distance x w ≤ ε := by
  intro hxy hxz
  intro hw
  match hw with
  | Or.inl ⟨hyw, hwz⟩ => exact distance_less_equal_between' hε hxy hxz (And.intro hyw hwz)
  | Or.inr ⟨hzw, hwy⟩ => exact distance_less_equal_between' hε hxz hxy (And.intro hzw hwy)
-/

-- TODO: Don't need the hw?
theorem distance_less_equal_multiply_left {ε w x y : ℚ} (_ : 0 < ε) (_ : w ≠ 0) :
    distance x y ≤ ε → distance (w * x) (w * y) ≤ (|w| * ε) := by
  intro hxy
  have := multiply_nonnegative_left_monotone (magnitude_nonnegative w) hxy
  simp only [distance] at this
  rw [← magnitude_multiply_equal_multiply_magnitude, ← subtract_definition, left_distributive, ← negate_multiply_equal_multiply_negate] at this
  exact this

theorem distance_less_equal_multiply_right {ε z x y : ℚ} (hε : 0 < ε) (hz : z ≠ 0) :
    distance x y ≤ ε → distance (x * z) (y * z) ≤ (ε * |z|) := by
  rw [multiply_commutative x z, multiply_commutative y z, multiply_commutative ε |z|]
  exact distance_less_equal_multiply_left hε hz

-- TODO: Need to revisit this one for understanding, formalized Tao's proof because of time.
theorem distance_less_equal_multiply {ε δ w x y z : ℚ} (hε : 0 < ε) (_ : 0 < δ) :
    distance x y ≤ ε → distance z w ≤ δ →
    distance (x * z) (y * w) ≤ (ε * |z| + δ * |x| + ε * δ) := by
  intro hxy hzw
  let a := y - x;
  have hy : y - x + x = a + x := congrArg (. + x) (rfl : a = y - x)
  rw [← subtract_definition, negate_add_cancel_right] at hy
  have ha : |a| ≤ ε := by simp only [a, ← distance_definition, distance_commutative, hxy]
  let b := w - z;
  have hw : w - z + z = b + z := congrArg (. + z) (rfl : b = w - z)
  rw [← subtract_definition, negate_add_cancel_right] at hw
  have hb : |b| ≤ δ := by simp only [b, ← distance_definition, distance_commutative w z]; exact hzw
  have hyw : y*w = a*b + a*z + x*b + x*z := by rw [hy, hw, right_distributive, left_distributive, left_distributive, ← add_associative]
  rw [distance_commutative, hyw, distance, ← subtract_definition, add_negate_cancel_right, add_commutative (a*b) (a*z), add_right_commutative, multiply_commutative x b]
  apply less_equal_transitive (magnitude_add_less_equal _ _)
  apply less_equal_transitive
  apply add_right_monotone (|a * b|) (magnitude_add_less_equal _ _)
  apply add_less_equal_add
  apply add_less_equal_add
  rw [magnitude_multiply_equal_multiply_magnitude a z]
  exact multiply_nonnegative_right_monotone (magnitude_nonnegative z) ha
  rw [magnitude_multiply_equal_multiply_magnitude b x]
  exact multiply_nonnegative_right_monotone (magnitude_nonnegative x) hb
  rw [magnitude_multiply_equal_multiply_magnitude a b]
  exact multiply_less_equal_multiply ha hb (magnitude_nonnegative _) (less_equal_of_less_than hε)

open Natural (zero successor)

def exponentiate : ℚ → ℕ → ℚ
  | _, Natural.zero => 1
  | x, Natural.successor n => (exponentiate x n) * x

instance : HPow Rational Natural Rational where
  hPow := exponentiate

theorem exponentiate_definition (x : ℚ) (a : ℕ) : (exponentiate x a) = x^a := rfl

theorem exponentiate_zero (x : ℚ) : x^(0 : ℕ) = 1 := rfl

theorem exponentiate_successor (x : ℚ) (n : ℕ) : x ^ (successor n) = x ^ n * x := rfl

theorem one_exponentiate (n : ℕ) : 1 ^ n  = (1 : ℚ) := by
  induction n with
  | zero => rw [Natural.zero_definition, exponentiate_zero]
  | successor n ih =>
    rw [← exponentiate_definition, exponentiate, multiply_one, exponentiate_definition, ih]

theorem exponentiate_add (x : ℚ) (n m : ℕ) : x^n * x^m = x^(n + m) := by
  induction n with
  | zero => simp [Natural.zero_definition, exponentiate_zero, one_multiply, Natural.zero_add]
  | successor n ih =>
    rw [Natural.successor_add, exponentiate_successor, exponentiate_successor]
    match Decidable.em (x = 0) with
    | Or.inl hx => simp [hx, multiply_zero, zero_multiply]
    | Or.inr _ => rw [multiply_right_commutative]; exact congrArg (. * x) ih

theorem exponentiate_multiply (x : ℚ) (n m : ℕ) : (x^n)^m = x^(n * m) := by
  induction m with
  | zero => simp [Natural.zero_definition, exponentiate_zero]
  | successor m ih =>
    rw [exponentiate_successor, Natural.multiply_successor, ← exponentiate_add]
    exact congrArg (. * x^n) ih

theorem multiply_exponentiate (x y : ℚ) (n : ℕ) : (x * y)^n = x^n * y^n := by
  induction n with
  | zero => simp [Natural.zero_definition, exponentiate_zero, multiply_one]
  | successor n ih =>
    simp [exponentiate_successor]
    rw [multiply_associative, multiply_left_commutative x, ← multiply_associative (x^n)]
    exact congrArg (. * (x*y)) ih

-- TODO: This is bad
theorem equal_zero_of_exponentiate_zero_of_positive {x : ℚ} {n : ℕ} : 0 < n → x^n = 0 → x = 0 := by
  induction n with
  | zero => intro hn; contradiction
  | successor n ih =>
    intro _ hx
    rw [exponentiate_successor] at hx
    match equal_zero_of_multiply_equal_zero hx with
    | Or.inl hxn =>
      match Natural.equal_zero_or_positive n with
      | Or.inl hn => rw [hn, exponentiate_zero] at hxn; contradiction
      | Or.inr hn => exact ih hn hxn
    | Or.inr h => exact h
    
theorem exponentiate_zero_of_equal_zero_of_positive {x : ℚ} {n : ℕ} (hn : 0 < n) (hx : x = 0) : x^n = 0 := by
  match n with
  | Natural.zero => contradiction
  | Natural.successor n => rw [exponentiate_successor, hx, multiply_zero]

theorem exponentiate_zero_equivalent_equal_zero_of_positive {x : ℚ} {n : ℕ} (hn : 0 < n) :
    x^n = 0 ↔ x = 0 :=
  ⟨equal_zero_of_exponentiate_zero_of_positive hn, exponentiate_zero_of_equal_zero_of_positive hn⟩
  
theorem exponentiate_nonnegative {x : ℚ} {n : ℕ} (hx : 0 ≤ x) : 0 ≤ x^n := by
  induction n with
  | zero => 
    rw [Natural.zero_definition, exponentiate_zero]
    decide
  | successor n ih =>
    rw [exponentiate_successor]
    have := multiply_nonnegative_right_monotone hx ih
    simp [zero_multiply] at this
    exact this

theorem exponentiate_positive {x : ℚ} {n : ℕ} (hx : 0 < x) : 0 < x^n := by
  induction n with
  | zero => simp [Natural.zero_definition, exponentiate_zero]; decide
  | successor n ih => 
    simp [exponentiate_successor]
    exact multiply_positive ih hx

theorem exponentiate_nonzero {x : ℚ} (hx : x ≠ 0) (n : ℕ) : x^n ≠ 0 := by
  induction n with
  | zero => rw [Natural.zero_definition, exponentiate_zero]; decide
  | successor n ih => 
    rw [exponentiate_successor]
    exact multiply_nonzero_of_nonzero ih hx

-- TODO: Figure out how to actually use the monotone definition, or change the name to reflect that its only the nonnegative part of the rationals
theorem exponentiate_nonnegative_monotone {x y : ℚ} (n : ℕ) (hx : 0 ≤ x) (hxy : x ≤ y) : x^n ≤ y^n := by
  induction n with
  | zero =>
    simp [Natural.zero_definition, exponentiate_zero]
    exact less_equal_reflexive 1
  | successor n ih =>
    simp [exponentiate_successor]
    apply multiply_less_equal_multiply ih hxy hx 
    exact exponentiate_nonnegative (less_equal_transitive hx hxy)

theorem exponentiate_nonnegative_strict_monotone {x y : ℚ} {n : ℕ} (hx : 0 ≤ x) (hxy : x < y) (hn : 0 < n) : x^n < y^n := by
  induction n with
  | zero => contradiction
  | successor n ih =>
    match Natural.equal_zero_or_positive n with
    | Or.inl hn =>
      simp [hn, exponentiate_successor, exponentiate_zero, one_multiply]
      exact hxy
    | Or.inr hn =>
      match less_than_or_equal_of_less_equal hx with
      | Or.inl hx =>
        simp [exponentiate_successor]
        apply multiply_less_than_multiply (ih hn) hxy hx
        exact exponentiate_positive (less_than_transitive hx hxy)
      | Or.inr hx => 
        rw [← hx, exponentiate_successor, multiply_zero]
        exact exponentiate_positive (hx.symm ▸ hxy)

theorem exponentiate_magnitude (x : ℚ) (n : ℕ) : |x^n| = |x|^n := by
  induction n with
  | zero => simp [Natural.zero_definition, exponentiate_zero]; rfl
  | successor n ih =>
    simp [exponentiate_successor, magnitude_multiply_equal_multiply_magnitude]
    exact congrArg (. * |x|) ih

theorem reciprocal_exponentiate (x : ℚ) (hx : x ≠ 0) (n : ℕ) : 
    (⟨x ^ n, exponentiate_nonzero hx n⟩⁻¹ : ℚ≠0).val = ((⟨x, hx⟩⁻¹ : ℚ≠0).val)^n := by
  induction n with
  | zero => rfl
  | successor n ih =>
    conv in x ^ n.successor => rw [exponentiate_successor]
    simp [exponentiate_successor]
    conv => lhs; rw [multiply_reciprocal ⟨x ^ n, exponentiate_nonzero hx n⟩ ⟨x, hx⟩, multiply_commutative]
    rw [ih]

def exponentiate' (x : ℚ≠0) (a : ℤ) : ℚ≠0 :=
  if ha : 0 ≤ a
  then
    let n := Integer.NonNegativeInteger.toNatural ⟨a, ha⟩
    ⟨exponentiate x.val n, exponentiate_nonzero x.property n⟩
  else
    let n := Integer.NonPositiveInteger.toNatural ⟨a, less_equal_of_not_greater_equal ha⟩
    reciprocal ⟨exponentiate x.val n, exponentiate_nonzero x.property n⟩

instance : HPow NonZeroRational Integer NonZeroRational where
  hPow := exponentiate'
  
theorem exponentiate'_definition (x : ℚ≠0) (a : ℤ) : (exponentiate' x a) = x^a := rfl

theorem exponentiate'_zero (x : ℚ≠0) : x^(0 : ℤ) = (⟨1, by decide⟩ : ℚ≠0) := rfl

-- TODO: Is there something wrong with the macros we've defined that we need to 
-- go fix? This is stupid
theorem one_exponentiate' (a : ℤ) : let one : ℚ≠0 := ⟨1, by decide⟩;
    one^a = one := by
  if h : 0 ≤ a
  then
    simp [← exponentiate'_definition, exponentiate', h, exponentiate_definition, one_exponentiate]
  else
    simp [← exponentiate'_definition, exponentiate', h, exponentiate_definition, one_exponentiate, reciprocal_one]

theorem exponentiate'_nonnegative (x : ℚ≠0) (a : ℤ) (ha : 0 ≤ a) :
  x^a = ⟨x^Integer.NonNegativeInteger.toNatural ⟨a, ha⟩, exponentiate_nonzero x.property (Integer.NonNegativeInteger.toNatural ⟨a, ha⟩)⟩ := by
  let ⟨x', hx⟩ := x
  simp [← exponentiate'_definition, exponentiate', ha, exponentiate_definition]
  
theorem exponentiate'_negative (x : ℚ≠0) (a : ℤ) (ha : a < 0) :
    let n := Integer.NonPositiveInteger.toNatural ⟨a, less_equal_of_less_than ha⟩
    x^a = ⟨x^n, exponentiate_nonzero x.property n⟩⁻¹ := by
  let ⟨x', hx⟩ := x
  simp [← exponentiate'_definition, exponentiate', not_less_equal_of_greater_than ha, exponentiate_definition]

theorem exponentiate'_negate (x : ℚ≠0) (a : ℤ) : x^(-a) = (x^a)⁻¹ := by
  let ⟨x', hx⟩ := x
  match less_than_trichotomous a 0 with
  | Or.inl ha =>
    simp [← exponentiate'_definition, exponentiate']
    have negate_a_nonnegative := less_equal_of_less_than <| Integer.negate_strict_antitone ha
    simp [← Integer.negate_zero] at negate_a_nonnegative
    simp [not_less_equal_of_greater_than ha, negate_a_nonnegative, reciprocal_involutive, Integer.NonPositiveInteger.toNatural]
  | Or.inr (Or.inl ha) =>
    simp [ha, ← Integer.negate_zero, exponentiate'_zero, reciprocal_one]
  | Or.inr (Or.inr ha) =>
    simp [← exponentiate'_definition, exponentiate']
    have not_negate_a_nonnegative := not_less_equal_of_greater_than <| Integer.negate_strict_antitone ha
    simp [← Integer.negate_zero] at not_negate_a_nonnegative
    simp [ less_equal_of_less_than ha, not_negate_a_nonnegative, Integer.NonPositiveInteger.toNatural]

theorem exponentiate'_add (x : ℚ≠0) (a b : ℤ) : (x^a).val * (x^b).val = (x^(a + b)).val := by
  /-
  Proof. By cases on a and b.
  Case 1. Suppose 0 ≤ a and 0 ≤ b. Apply `exponentiate_add` and `toNatural_add`.
  Case 2. Suppose a < 0 and b < 0. Then apply `multiply_reciprocal` to combine 
    the terms on the left hand side, reducing to case 1.
  Case 3. 
    It suffices to assume a < 0 and 0 ≤ b. This follows from commutativity of addition 
    and multiplication. Then we have two subcases.

    If a + b < 0, then we must show ⊢ 1/(x^-a) * x^b = 1/(x^-(a+b)). Observing that -(a + b) is 
    positive and can therefore be used in the natural exponent operation, notice that we 
    have x^b * x^-(a+b) = x^(b + -(a + b)) = x^-a. Substitution gives
    ⊢ 1/(x^b * x^-(a+b)) * x^b = 1/(x^-(a+b)).
    Rewrite using `multiply_inverse` and simplify.

    A similar argument applies when 0 ≤ a + b, but we substitute for x^b instead.
  -/
  have h1 {c d : ℤ} (hc : c < 0) (hd : 0 ≤ d) : (x^c).val * (x^d).val = (x^(c + d)).val := by
    match less_than_or_less_equal (c + d) 0 with
    | Or.inl hcd =>
      simp [← exponentiate'_definition, exponentiate', hd, not_less_equal_of_greater_than hc, not_less_equal_of_greater_than hcd, exponentiate_definition, Integer.NonPositiveInteger.toNatural]
      let dn := Integer.NonNegativeInteger.toNatural ⟨d, hd⟩
      have hcdn := less_equal_of_less_than <| Integer.negate_strict_antitone hcd
      let cdn := Integer.NonNegativeInteger.toNatural ⟨-(c + d), hcdn⟩
      have := exponentiate_add x.val dn cdn
      simp [dn, cdn, Integer.NonNegativeInteger.toNatural_add, Integer.negate_add, Integer.add_commutative (-c), Integer.add_negate_cancel_left] at this
      simp [exponentiate_definition, ← this]
      simp [← Integer.negate_add, Integer.add_commutative]
      rw [multiply_reciprocal ⟨(x.val ^ dn), exponentiate_nonzero x.property dn⟩ ⟨x.val ^ cdn, exponentiate_nonzero x.property cdn⟩]
      -- CONVERSION MODE!? HOW DID I NOT KNOW ABOUT THIS... I HAVE SUFFERED
      conv => lhs; rw [multiply_associative]; arg 2; rw [multiply_commutative, multiply_inverse ⟨x.val ^ dn, exponentiate_nonzero x.property dn⟩]
      simp [multiply_one]
    | Or.inr hcd =>
      simp [← exponentiate'_definition, exponentiate', hd, not_less_equal_of_greater_than hc, hcd, exponentiate_definition, Integer.NonPositiveInteger.toNatural]
      let cn := Integer.NonNegativeInteger.toNatural ⟨-c, less_equal_of_less_than <| Integer.negate_strict_antitone hc⟩
      let cdn := Integer.NonNegativeInteger.toNatural ⟨c + d, hcd⟩
      have := exponentiate_add x.val cn cdn
      simp [cn, cdn, Integer.NonNegativeInteger.toNatural_add, Integer.negate_add_cancel_left] at this
      rw [← this, ← multiply_associative]
      conv => lhs; arg 1; rw [multiply_commutative, multiply_inverse ⟨x.val ^ cn, _⟩]
      simp [one_multiply]
  match less_than_or_less_equal a 0, less_than_or_less_equal b 0 with
  | Or.inl ha, Or.inl hb =>
    have hab : a + b < 0 := Integer.add_less_than_add ha hb
    simp [← exponentiate'_definition, exponentiate', not_less_equal_of_greater_than ha, not_less_equal_of_greater_than hb, not_less_equal_of_greater_than hab, ← multiply_reciprocal, multiply_commutative]
    apply congrArg (λ x : ℚ≠0 => x⁻¹.val)
    simp [← Integer.NonPositiveInteger.toNatural_add ⟨a, less_equal_of_less_than ha⟩ ⟨b, less_equal_of_less_than hb⟩, exponentiate_definition]
    apply Subtype.eq
    exact exponentiate_add _ _ _
  | Or.inl ha, Or.inr hb =>
    exact h1 ha hb
  | Or.inr ha, Or.inl hb =>
    rw [multiply_commutative, Integer.add_commutative]
    exact h1 hb ha
  | Or.inr ha, Or.inr hb =>
    have hab : 0 ≤ a + b := Integer.add_less_equal_add ha hb
    simp [← exponentiate'_definition, exponentiate', ha, hb, hab, ← Integer.NonNegativeInteger.toNatural_add ⟨a, ha⟩ ⟨b, hb⟩]
    exact exponentiate_add _ _ _

theorem exponentiate'_multiply (x : ℚ≠0) (a b : ℤ) : (x^a)^b = x^(a * b) := by
  -- Trick was to develop `inverse_multiply`
  -- Also had a lot of trouble with exponentiate' match definition to the point 
  -- that I just redefined it to avoid the trouble
  match less_than_or_less_equal a 0, less_than_or_less_equal b 0 with
  | Or.inl ha, Or.inl hb =>
    let bn := Integer.NonPositiveInteger.toNatural ⟨b, less_equal_of_less_than hb⟩
    have hab := less_equal_of_less_than <| Integer.multiply_negative ha hb
    apply Subtype.eq
    rw [exponentiate'_negative _ b hb, reciprocal_exponentiate _ (x^a).property bn]
    simp [exponentiate'_negative x a ha, Subtype.eta, reciprocal_involutive]
    simp [← exponentiate'_definition, exponentiate', hab, exponentiate_definition, bn, 
      Integer.NonPositiveInteger.toNatural, exponentiate_multiply, Integer.NonNegativeInteger.toNatural_multiply]
    simp [← Integer.negate_multiply_equal_negate_multiply, ← Integer.negate_multiply_equal_multiply_negate]
  | Or.inl ha, Or.inr hb =>
    if hb' : b = 0
    then
      simp [hb', exponentiate'_zero, Integer.multiply_zero]
    else
      let hb'' := less_than_of_less_equal_of_not_equal hb (Ne.symm hb')
      let hab := Integer.multiply_negative_of_negative_of_positive ha hb''
      simp [← exponentiate'_definition, exponentiate', not_less_equal_of_greater_than ha, hb, not_less_equal_of_greater_than hab, exponentiate_definition] 
      simp [← reciprocal_exponentiate, Integer.NonPositiveInteger.toNatural]
      simp [exponentiate_multiply, Integer.NonNegativeInteger.toNatural_multiply]
      simp [Subtype.eta, Integer.negate_multiply_equal_negate_multiply]
  | Or.inr ha, Or.inl hb =>
    if ha' : a = 0
    then
      simp [ha', Integer.zero_multiply, exponentiate'_zero, one_exponentiate']
    else
      have ha'' := less_than_of_less_equal_of_not_equal ha (Ne.symm ha')
      let hab := Integer.multiply_negative_of_positive_of_negative ha'' hb
      simp [← exponentiate'_definition, exponentiate', ha, not_less_equal_of_greater_than hb, not_less_equal_of_greater_than hab, exponentiate_definition] 
      simp [Integer.NonPositiveInteger.toNatural, exponentiate_multiply, Integer.NonNegativeInteger.toNatural_multiply]
      simp [Integer.negate_multiply_equal_multiply_negate]
  | Or.inr ha, Or.inr hb =>
    simp [← exponentiate'_definition, exponentiate', ha, hb, Integer.multiply_nonnegative ha hb]
    let an := Integer.NonNegativeInteger.toNatural ⟨a, ha⟩
    let bn := Integer.NonNegativeInteger.toNatural ⟨b, hb⟩
    simp [exponentiate_definition, an, bn, ← Integer.NonNegativeInteger.toNatural_multiply ⟨a, ha⟩ ⟨b, hb⟩, exponentiate_multiply]
  
theorem multiply_exponentiate' (x y : ℚ≠0) (a : ℤ) : 
    let xy_nonzero := multiply_nonzero_of_nonzero x.property y.property
    let xaya_nonzero := multiply_nonzero_of_nonzero (x^a).property (y^a).property
    (⟨x.val * y.val, xy_nonzero⟩^a : ℚ≠0) = (⟨(x^a).val * (y^a).val, xaya_nonzero⟩ : ℚ≠0) := by
  if ha : 0 ≤ a
  then
    simp [← exponentiate'_definition, exponentiate', ha, exponentiate_definition, multiply_exponentiate]
  else
    simp [← exponentiate'_definition, exponentiate', ha, exponentiate_definition]
    simp [← multiply_reciprocal, multiply_commutative, multiply_exponentiate, Subtype.eta]


theorem reciprocal_exponentiate' (x : ℚ≠0) (a : ℤ) : (x ^ a)⁻¹ = (x⁻¹)^a := by
  if ha : 0 ≤ a
  then
    simp [← exponentiate'_definition, exponentiate', ha, exponentiate_definition]
    apply Subtype.eq
    exact reciprocal_exponentiate x.val x.property (Integer.NonNegativeInteger.toNatural ⟨a, ha⟩)
  else
    simp [← exponentiate'_definition, exponentiate', ha, exponentiate_definition]
    simp [reciprocal_involutive]
    let ⟨x', hx⟩ := x
    have ha' := less_equal_of_not_greater_equal ha
    simp [← reciprocal_exponentiate x' hx (Integer.NonPositiveInteger.toNatural ⟨a, ha'⟩), Subtype.eta, reciprocal_involutive]

theorem exponentiate'_nonnegative_monotone {x y : ℚ} (a : ℤ) (ha : 0 ≤ a) (hx : 0 < x) (hxy : x ≤ y) : 
    let hx' := Ne.symm <| not_equal_of_less_than hx
    let hy' := Ne.symm <| not_equal_of_less_than <| less_than_of_less_than_of_less_equal hx hxy
    let x' : ℚ≠0 := ⟨x, hx'⟩
    let y' : ℚ≠0 := ⟨y, hy'⟩
    (x'^a).val ≤ (y'^a).val := by
  simp [← exponentiate'_definition, exponentiate', ha, exponentiate_definition]
  let an := Integer.NonNegativeInteger.toNatural ⟨a, ha⟩
  exact exponentiate_nonnegative_monotone an (less_equal_of_less_than hx) hxy

theorem exponentiate'_negative_antitone {x y : ℚ} (a : ℤ) (ha : a < 0) (hx : 0 < x) (hxy : x ≤ y) : 
    let hx' := Ne.symm <| not_equal_of_less_than hx
    let hy' := Ne.symm <| not_equal_of_less_than <| less_than_of_less_than_of_less_equal hx hxy
    let x' : ℚ≠0 := ⟨x, hx'⟩
    let y' : ℚ≠0 := ⟨y, hy'⟩
    (y'^a).val ≤ (x'^a).val := by
  simp [← exponentiate'_definition, exponentiate', ha, exponentiate_definition]
  simp [not_less_equal_of_greater_than ha, Integer.NonPositiveInteger.toNatural]
  let an := Integer.NonNegativeInteger.toNatural ⟨-a, less_equal_of_less_than <| Integer.negate_strict_antitone ha⟩
  have : x ^ an ≤ y ^ an := exponentiate_nonnegative_monotone an (less_equal_of_less_than hx) hxy
  exact reciprocal_positive_antitone (exponentiate_positive hx) this

-- TODO: Analogous lemmas for other ordering possibilities

-- TODO: But rational equality is decidable! So we can use contradiction
/- TODO:

This one's especially difficult to prove without using contradiction?
The only way I'm seeing to do it is to factor x^n - y^n = (x - y)*{sum}.

See https://math.stackexchange.com/questions/117660/proving-xn-yn-x-yxn-1-xn-2-y-x-yn-2-yn-1

Then I think we can show that the sum is nonzero, and since x^n - y^n
= 0, we have x - y = 0. But this will require a ton of sum lemmas that
we don't have, so I'm going to postpone this one for now
unfortunately.
theorem exponentiate'_positive_nonzero_injective : ∀ {x y : ℚ} {a : ℤ} 
    (hx : 0 < x) (hy : 0 < y) (ha : a ≠ 0),
    let x' : ℚ≠0 := ⟨x, Ne.symm <| not_equal_of_less_than hx⟩
    let y' : ℚ≠0 := ⟨y, Ne.symm <| not_equal_of_less_than hy⟩
    x'^a = y'^a → x = y := by
  intro x y a hx hy ha x' y' h
  suffices x'.val * (y'⁻¹).val = 1 by
  { have h1 := congrArg (. * y) this
    simp [one_multiply, multiply_associative, multiply_commutative y'⁻¹.val] at h1
    have h2 : y = y'.val := rfl
    rw [h2, multiply_inverse, multiply_one] at h1
    exact h1 }
  let f : ℚ≠0 → ℚ≠0 := λ z => ⟨z.val * (y' ^ (-a)).val, multiply_nonzero_of_nonzero z.property (y' ^ (-a)).property⟩
  have h3 := congrArg f h
  simp [f] at h3
  simp [exponentiate'_add, Integer.add_inverse, exponentiate'_zero] at h3
  simp [exponentiate'_negate, reciprocal_exponentiate', ← multiply_exponentiate'] at h3
  exact equal_one_of_exponentiate_positive_equal_one a (multiply_positive hx (reciprocal_positive y')) ha h3
-/
  
theorem exponentiate'_magnitude (x : ℚ≠0) (a : ℤ) : 
    let x' : ℚ≠0 := ⟨|x.val|, mt zero_of_magnitude_zero x.property⟩
    |(x^a).val| = (x'^a).val := by
  if ha : 0 ≤ a
  then
    simp [← exponentiate'_definition, exponentiate', ha, exponentiate_definition, exponentiate_magnitude]
  else
    simp [← exponentiate'_definition, exponentiate', ha, exponentiate_definition, Integer.NonPositiveInteger.toNatural] 
    rw [magnitude_reciprocal]
    congr
    simp [exponentiate_magnitude]

-- TODO:
  -- Proposition 4.4.1 theorem exists_integer_between : ∀ x : ℚ, ∃! a : ℤ, ↑a ≤ x ∧ x ≤ ↑a + 1 := by
  -- Proposition 4.4.2
  -- Proposition 4.4.3
  -- Proposition 4.4.4
  -- Proposition 4.4.5
  
-- TODO: Might as well do a a ⟦a * b / c * d⟧ = ⟦a/c⟧ * ⟦b/c⟧ theorem too

theorem lift_add (a b c : ℤ) (hc : c ≠ 0) : 
    Quotient.mk instanceSetoidRationalEquivalent (a + b, ⟨c, hc⟩) = add ⟦(a, ⟨c, hc⟩)⟧ ⟦(b, ⟨c, hc⟩)⟧ := by
  simp [add]
  apply Quotient.sound
  show (a + b) * (c * c) = (a * c + b * c) * c
  rw [← Integer.multiply_associative, Integer.right_distributive]

/-

def mixed (x : ℚ) :
    Σ' ar : ℤ × ℚ,
    let (a, r) := ar
    ↑a + r = x ∧ 0 ≤ r ∧ r < 1 :=
  let mixed' 
    | ⟨a, b, hb⟩ =>
      let ⟨(q, r), hqr, hr1', hr2'⟩ := Integer.divideWithRemainder a b hb
      have hx := by
        rw [hqr, lift_add]
        have hq : Quot.mk Setoid.r (q * b, (⟨b, hb⟩ : ℤ≠0)) = Quot.mk Setoid.r (q, ⟨1, by decide⟩) := by
          apply Quotient.sound
          show (q * b) * 1 = q * b
          rw [Integer.multiply_one]
        have hbr : Quot.mk Setoid.r (b
        rw [hq, ← ofInteger, add_definition]
      have hr1 := sorry
      have hr2 := sorry
      ⟨(q, ⟦(r, ⟨b, hb⟩)⟧), hx, hr1, hr2⟩
  Quotient.recOn x mixed' <| by
  sorry
  
def floor (x : ℚ) : ℤ := 
  let ⟨(a, _), _⟩ := mixed x
  a
  
theorem floor_less_equal (x : ℚ) : ↑(floor x) ≤ x := sorry

theorem less_equal_floor_add_one (x : ℚ) : x < ↑(floor x) + 1 := sorry
  
theorem floor_greatest_less_equal (x : ℚ) : ∀ a : ℤ, ↑a ≤ x → a ≤ floor x := sorry

def ceiling (x : ℚ) : ℤ :=
  let xf := floor x
  if x = ↑xf then
    xf
  else
    xf + 1

theorem ceiling_greater_equal (x : ℚ) : x ≤ ↑(ceiling x) := sorry

theorem ceiling_least_greater_equal (x : ℚ) : ∀ a : ℤ, x ≤ ↑a → ceiling x ≤ a := sorry

theorem ceiling_less_equal_floor_add_one (x : ℚ) : ceiling x ≤ (floor x) + 1 := sorry

theorem exists_integer_between (x : ℚ) : ∃! a : ℤ, ↑a ≤ x ∧ x < ↑a + 1 := by
  apply ExistsUnique.introduction (floor x)
  . constructor
    . exact floor_less_equal x
    . exact less_equal_floor_add_one x
  . intro a
    if ha : a = floor x then
      intro _
      exact ha
    else
      suffices ∀ {a b : ℤ}, a < b → ¬(↑b ≤ x ∧ x < ↑a + 1) by
      { intro h
        match less_than_connected ha with 
        | Or.inl ha =>
          exact absurd (And.intro (floor_less_equal x) h.right) (this ha)
        | Or.inr ha =>
          exact absurd (And.intro h.left (less_equal_floor_add_one x)) (this ha) }
      intro a b hab ⟨hl, hr⟩
      have hl' := ofInteger_monotone <| Integer.less_than_equivalent_add_one_less_equal.mp hab
      have hr' := less_than_of_less_equal_of_less_than hl hr
      have h1 : 1 = ofInteger 1 := rfl
      rw [h1, ← ofInteger_add] at hr'
      have := less_than_of_less_than_of_less_equal hr' hl'
      exact False.elim <| less_than_irreflexive _ <| this
-/
