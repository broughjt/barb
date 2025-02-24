import Barb.Algebra
import Barb.Data.Natural
import Barb.Data.Option
import Barb.Function
import Barb.Logic
import Barb.Quotient
import Barb.Syntax

open Natural (zero successor)

def IntegerEquivalent : (ℕ × ℕ) → (ℕ × ℕ) → Prop
  | (n, m), (k, l) => n + l = k + m

theorem IntegerEquivalent.reflexive : Reflexive IntegerEquivalent :=
  λ _ => rfl

theorem IntegerEquivalent.symmetric : Symmetric IntegerEquivalent := Eq.symm

theorem IntegerEquivalent.transitive : Transitive IntegerEquivalent
  | (n, m), (k, l), (p, q), (h₁ : n + l = k + m), (h₂ : k + q = p + l) => by
    apply Natural.add_left_cancel (n := k + l)
    calc
      (k + l) + (n + q) = (n + l) + (k + q) := by simp [Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative]
      _ = (k + m) + (p + l) := by simp [h₁, h₂]
      _ = (k + l) + (p + m) := by simp [Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative]

theorem IntegerEquivalent.is_equivalence : Equivalence IntegerEquivalent :=
  { refl := IntegerEquivalent.reflexive, symm := IntegerEquivalent.symmetric, trans := IntegerEquivalent.transitive }

instance instanceHasEquivIntegerEquivalent : HasEquiv (ℕ × ℕ) where
  Equiv := IntegerEquivalent

instance instanceSetoidIntegerEquivalent : Setoid (ℕ × ℕ) where
  r := IntegerEquivalent
  iseqv := IntegerEquivalent.is_equivalence

theorem IntegerEquivalent.definition : (a ≈ b) = IntegerEquivalent a b := rfl

instance decideIntegerEquivalent (a b : ℕ × ℕ) : Decidable (a ≈ b) :=
  let (n, m) := a
  let (k, l) := b
  Natural.decideEqual (n + l) (k + m)

instance decideIntegerEquivalentQuotientEqual : DecidableEq (Quotient instanceSetoidIntegerEquivalent) := inferInstance

-- This is basically the one line of consequence in this block
def Integer := Quotient instanceSetoidIntegerEquivalent

namespace Integer

notation "ℤ" => Integer

instance decideEqual : DecidableEq Integer := decideIntegerEquivalentQuotientEqual

instance : OfNat Integer n where
  ofNat := ⟦(Natural.fromNat n, 0)⟧
  
instance Zero : Integer := ⟦(0, 0)⟧

instance One : Integer := ⟦(1, 0)⟧

def negate : ℤ → ℤ :=
  let negate' := λ ((n, m) : ℕ × ℕ) => (m, n)
  Quotient.map negate' <| by
  intro (n, m) (n', m') (h : n + m' = n' + m)
  show m + n' = m' + n
  simp [Natural.add_commutative, h]

instance : Neg Integer where
  neg := negate

@[simp] theorem negate_definition : negate a = -a := rfl

def add : ℤ → ℤ → ℤ :=
  let add' := λ ((n, m) : ℕ × ℕ) ((k, l) : ℕ × ℕ) => (n + k, m + l)
  Quotient.map₂ add' <| by
  intro (n, m) (n', m') (h₁ : n + m' = n' + m)
  intro (k, l) (k', l') (h₂ : k + l' = k' + l)
  show (n + k) + (m' + l') = (n' + k') + (m + l)
  calc
    (n + k) + (m' + l')
      = (n + m') + (k + l') := by simp [Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative]
    _ = (n' + m) + (k + l') := congrArg (. + _) h₁
    _ = (n' + m) + (k' + l) := congrArg (_ + .) h₂
    _ = (n' + k') + (m + l) := by simp [Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative]

instance : Add Integer where add := add

@[simp] theorem add_definition : add a b = a + b := rfl

def multiply : ℤ → ℤ → ℤ :=
  let multiply' := λ ((n, m) : ℕ × ℕ) ((k, l) : ℕ × ℕ) => (n * k + m * l, n * l + m * k)
  Quotient.map₂ multiply' <| by
  intro (n, m) (n', m') (h₁ : n + m' = n' + m)
  intro (k, l) (k', l') (h₂ : k + l' = k' + l)
  apply Natural.add_left_cancel (n := (n * l + m * k) + (n' * k + m' * l))
  have h₃ : (n * k + m * l) + (n' * l + m' * k) = (n * l + m * k) + (n' * k + m' * l) := calc
    (n * k + m * l) + (n' * l + m' * k)
      = (n + m') * k + (n' + m) * l := by simp [Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative, Natural.right_distributive]
    _ = (n' + m) * k + (n + m') * l := by simp [h₁]
    _ = (n * l + m * k) + (n' * k + m' * l) := by simp [Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative, Natural.right_distributive]
  calc
    ((n * l + m * k) + (n' * k + m' * l)) + ((n * k + m * l) + (n' * l' + m' * k'))
      = (n * l + m * k) + ((n * k + m * l) + (n' * (k + l') + m' * (k' + l))) :=
        by simp [Natural.add_associative, Natural.add_commutative, Natural.left_distributive, Natural.add_left_commutative]
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * (k' + l) + m' * (k + l'))) := by simp [h₂]
    _ = ((n * k + m * l) + (n' * l + m' * k)) + ((n' * k' + m' * l') + (n * l + m * k)) :=
        by simp [Natural.add_associative, Natural.add_commutative, Natural.left_distributive, Natural.add_left_commutative]
    _ = ((n * l + m * k) + (n' * k + m' * l)) + ((n' * k' + m' * l') + (n * l + m * k)) := congrArg (. + _) h₃

instance : Mul Integer where mul := multiply

@[simp] theorem multiply_definition : multiply a b = a * b := rfl

theorem add_commutative : ∀ (a b : ℤ), a + b = b + a := by
  apply Quotient.ind₂
  intro (n, m) (k, l)
  apply Quotient.sound
  show (n + k) + (l + m) = (k + n) + (m + l)
  simp [Natural.add_commutative]

theorem add_associative : ∀ (a b c : ℤ), (a + b) + c = a + (b + c) := by
  apply Quotient.ind₃
  intro (n, m) (k, l) (o, p)
  apply Quotient.sound
  show ((n + k) + o) + (m + (l + p)) = (n + (k + o)) + ((m + l) + p)
  simp [Natural.add_associative]

theorem add_zero : ∀ (a : ℤ), a + 0 = a := by
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

theorem multiply_commutative : ∀ (a b : ℤ), a * b = b * a := by
  apply Quotient.ind₂
  intro (n, m) (k, l)
  apply Quotient.sound
  show (n * k + m * l) + (k * m + l * n) = (k * n + l * m) + (n * l + m * k)
  simp [Natural.add_commutative, Natural.multiply_commutative]

theorem multiply_associative : ∀ (a b c : ℤ), (a * b) * c = a * (b * c) := by
  intro a b c
  let i := Quotient.mk instanceSetoidIntegerEquivalent
  suffices ∀ (a b c : ℕ × ℕ), multiply (multiply (i a) (i b)) (i c) = multiply (i a) (multiply (i b) (i c))
  from Quotient.inductionOn₃ a b c this
  intro (n, m) (k, l) (p, q)
  apply Quotient.sound
  show ((n*k + m*l)*p + (n*l + m*k)*q) + (n*(k*q + l*p) + m*(k*p + l*q))
    = (n*(k*p + l*q) + m*(k*q + l*p)) + ((n*k + m*l)*q + (n*l + m*k)*p)
  let d := (n*k + m*l)*p + (n*l + m*k)*q
  let f := n*(k*p + l*q) + m*(k*q + l*p)
  let e := n*(k*q + l*p) + m*(k*p + l*q)
  let g := (n*k + m*l)*q + (n*l + m*k)*p
  have r {u v w x y z : ℕ} : (u*w + v*x)*y + (u*x + v*w)*z = u*(w*y + x*z) + v*(w*z + x*y) := calc
    (u*w + v*x)*y + (u*x + v*w)*z = u*w*y + v*x*y + u*x*z + v*w*z := by simp [Natural.add_associative, Natural.right_distributive]
    _ = u*(w*y) + u*(x*z) + v*(w*z) + v*(x*y) := by simp [Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative, Natural.multiply_associative]
    _ = u*(w*y + x*z) + v*(w*z + x*y) := by simp [Natural.left_distributive, Natural.add_associative]
  have hdf : d = f := calc
    d = (n*k + m*l)*p + (n*l + m*k)*q := rfl
    _ = n*(k*p + l*q) + m*(k*q + l*p) := r
    _ = f := rfl
  have heg : e = g := calc
    e = n*(k*q + l*p) + m*(k*p + l*q) := rfl
    _ = (n*k + m*l)*q + (n*l + m*k)*p := r.symm
    _ = g := rfl
  show d + e = f + g
  simp [hdf, heg]

theorem multiply_one : ∀ (a : ℤ), a * 1 = a := by
  apply Quotient.ind
  intro (n, m)
  apply Quotient.sound
  show (n * 1 + m * 0) + m = n + (n * 0 + m * 1)
  simp [Natural.add_associative, Natural.zero_add, Natural.multiply_one, Natural.multiply_zero]

theorem left_distributive : ∀ (a b c : ℤ), a * (b + c) = a * b + a * c := by
  apply Quotient.ind₃
  intro (n, m) (k, l) (p, q)
  apply Quotient.sound
  show (n*(k + p) + m*(l + q)) + ((n*l + m*k) + (n*q + m*p)) = ((n*k + m*l) + (n*p + m*q)) + (n*(l + q) + m*(k + p))
  simp [Natural.left_distributive, Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative]

theorem right_distributive : ∀ (a b c : ℤ), (a + b) * c = a * c + b * c := by
  intro a b c
  rw [multiply_commutative, left_distributive, multiply_commutative c a, multiply_commutative c b]

instance commutativeRing : CommutativeRing Integer where
  add_commutative := add_commutative
  add_associative := add_associative
  add_zero := add_zero
  add_inverse := add_inverse

  multiply_commutative := multiply_commutative
  multiply_associative := multiply_associative
  multiply_one := multiply_one

  left_distributive := left_distributive
  right_distributive := right_distributive

theorem zero_add (a : ℤ) : 0 + a = a := by
  rw [add_commutative, add_zero]

theorem add_left_commutative (n m k : ℤ) : n + (m + k) = m + (n + k) := by
  rw [← add_associative, add_commutative n m, add_associative]

theorem add_right_commutative (n m k : ℤ) : (n + m) + k = (n + k) + m := by
  rw [add_associative, add_commutative m k, ← add_associative]

theorem add_inverse_left (a : ℤ) : -a + a = 0 := by
  rw [add_commutative, add_inverse]

theorem add_left_cancel {a b c : ℤ} (h : a + b = a + c) : b = c := by
  have : -a + (a + b) = -a + (a + c) := by rw [h]
  simp [← add_associative, add_inverse_left, zero_add] at this
  exact this

theorem add_right_cancel {a b c : ℤ} (h : a + c = b + c) : a = b := by
  rewrite [add_commutative a c, add_commutative b c] at h
  exact add_left_cancel h

theorem negate_add_cancel_left (a b : ℤ) : -a + (a + b) = b := by
  rw [← add_associative (-a) a b, add_inverse_left, zero_add]

theorem negate_add_cancel_right (a b : ℤ) : (a + -b) + b = a := by
  rw [add_associative, add_inverse_left, add_zero]

theorem add_negate_cancel_left (a b : ℤ) : a + (-a + b) = b := by
  rw [← add_associative, add_inverse, zero_add]

theorem add_negate_cancel_right (a b : ℤ) : (a + b) + -b = a := by
  rw [add_associative, add_inverse, add_zero]

theorem multiply_zero : ∀ (a : ℤ), a * 0 = 0 := by
  apply Quotient.ind
  intro (n, m)
  apply Quotient.sound
  show (n*0 + m*0) + 0 = 0 + (n*0 + m*0)
  simp [Natural.add_zero, Natural.multiply_zero]

theorem zero_multiply (a : ℤ) : 0 * a = 0 := by
  rw [multiply_commutative, multiply_zero]

theorem one_multiply (a : ℤ) : 1 * a = a := by
  rw [multiply_commutative, multiply_one]

def subtract (a b : ℤ) : ℤ := a + (-b)

instance : Sub Integer where sub := subtract

theorem subtract_definition (a b : ℤ) : a + (-b) = a - b := rfl

theorem negate_zero : (0 : ℤ) = (-0 : ℤ) := rfl

theorem negate_involutive : Involutive negate := by
  apply Quotient.ind
  intro (n, m)
  rfl

@[simp]
theorem negate_negate : ∀ a : ℤ, - -a = a := λ a => negate_involutive a

theorem negate_injective : Injective negate := by
  unfold Injective
  intro x y h
  have := congrArg negate h
  simp at this
  exact this

theorem subtract_self (a : ℤ) : a - a = 0 := add_inverse a

theorem subtract_zero (a : ℤ) : a - 0 = a := by
  rw [← subtract_definition, ← negate_zero, add_zero]

theorem zero_subtract (a : ℤ) : 0 - a = -a := by
  rw [← subtract_definition, zero_add]

theorem negate_equal_of_add_equal_zero {a b : ℤ} (h : a + b = 0) : a = -b := by
  rw [← add_zero a, ← add_inverse (b), ← add_associative, h, zero_add]

theorem subtract_equal_zero_of_equal {a b : ℤ} (h : a = b) : a - b = 0 := by
  rw [← h, subtract_self]

theorem equal_of_subtract_equal_zero {a b : ℤ} (h : a - b = 0) : a = b := by
  rw [← add_zero a, ← add_inverse b, add_commutative b, ← add_associative, subtract_definition, h, zero_add]

theorem negate_add (a b : ℤ) : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_inverse, add_associative, ← add_associative b (-a) (-b), add_commutative b (-a),
     ← add_associative a, ← add_associative, add_inverse, zero_add, add_inverse]

theorem subtract_subtract (a b c : ℤ) : (a - b) - c = a - (b + c) := by
  apply Eq.symm
  rw [← subtract_definition, negate_add, ← add_associative, subtract_definition, subtract_definition]

theorem negate_subtract {a b : ℤ} : -(a - b) = b - a := by
  rw [← subtract_definition, negate_add, negate_negate, add_commutative, subtract_definition]

theorem subtract_subtract_self (a b : ℤ) : a - (a - b) = b := by
  rw [← subtract_definition, negate_subtract, ← subtract_definition,
    add_commutative (b) (-a), add_negate_cancel_left]

theorem negate_multiply_equal_negate_multiply (a b : ℤ) : -(a * b) = -a * b := by
  apply Eq.symm
  apply negate_equal_of_add_equal_zero
  rw [← right_distributive, add_commutative, add_inverse, zero_multiply]

theorem negate_multiply_equal_multiply_negate (a b : ℤ) : -(a * b) = a * -b := by
  rw [multiply_commutative, negate_multiply_equal_negate_multiply, multiply_commutative]

theorem subtract_multiply (a b c : ℤ) : (a - b) * c = a * c - b * c := by
  rw [← subtract_definition, right_distributive, ← negate_multiply_equal_negate_multiply, subtract_definition]

theorem multiply_subtract (a b c : ℤ) : a * (b - c) = a * b - a * c := by
  rw [multiply_commutative a _, subtract_multiply, multiply_commutative b a, multiply_commutative a c]

theorem equal_of_unlift_equal_zero {n m : ℕ} : ⟦(n, m)⟧ = (0 : ℤ) → n = m := by
  intro h
  rw [← Natural.add_zero n, ← Natural.zero_add m]
  exact Quotient.exact h

theorem equal_zero_of_lift_equal {n m : ℕ} : n = m → ⟦(n, m)⟧ = (0 : ℤ) := by
  intro h
  rw [← Natural.add_zero n, ← Natural.zero_add m] at h
  exact Quotient.sound h

theorem equal_zero_of_multiply_equal_zero : ∀ {a b : ℤ}, a * b = 0 → a = 0 ∨ b = 0 := by
  apply Quotient.ind₂
  intro (n, m) (k, l) h'
  have h := equal_of_unlift_equal_zero h'
  apply Or.implies equal_zero_of_lift_equal equal_zero_of_lift_equal
  have f {w x y z : ℕ} (h_less : w < x) (h_equivalent : w*y + x*z = w*z + x*y) : y = z := by
  { let ⟨a, h_positive, (h_exists : w + a = x)⟩ := Natural.equal_add_positive_of_less_than h_less
    apply (Natural.multiply_left_cancel . h_positive)
    apply Natural.add_left_cancel (n := w*y + w*z)
    rw [← h_exists, Natural.right_distributive, ← Natural.add_associative, Natural.right_distributive,
      Natural.add_left_commutative, ← Natural.add_associative] at h_equivalent
    exact h_equivalent.symm }
  match less_than_trichotomous n m with
  | Or.inl h_less => exact Or.inr (f h_less h)
  | Or.inr (Or.inl h_equal) =>
    apply Or.inl
    simp [h_equal, Natural.add_zero, Natural.zero_add]
  | Or.inr (Or.inr h_greater) =>
    apply Or.inr
    rw [Natural.add_commutative (n*l) (m*k), Natural.add_commutative (n*k) (m*l)] at h
    exact f h_greater h.symm

theorem multiply_equal_zero_of_equal_zero : ∀ {a b : ℤ}, a = 0 ∨ b = 0 → a * b = 0 := by
  apply Quotient.ind₂
  intro (n, m) (k, l) h'
  have h := Or.implies equal_of_unlift_equal_zero equal_of_unlift_equal_zero h'
  rw [← multiply_definition]
  simp [multiply, Quotient.map₂]
  apply equal_zero_of_lift_equal
  match h with
  | Or.inl hnm => rw [hnm, Natural.add_commutative]
  | Or.inr hkl => rw [hkl]

theorem multiply_left_commutative (n m k : ℤ) : n * (m * k) = m * (n * k) := by
  rw [← multiply_associative, multiply_commutative n m, multiply_associative]

theorem multiply_right_commutative (n m k : ℤ) : (n * m) * k = (n * k) * m := by
  rw [multiply_associative, multiply_commutative m k, ← multiply_associative]

theorem multiply_left_cancel {a b c : ℤ} (h : a * b = a * c) (a_nonzero : a ≠ 0) : b = c := by
  suffices c - b = 0 from (equal_of_subtract_equal_zero this).symm
  apply (Or.resolve_left . a_nonzero)
  apply equal_zero_of_multiply_equal_zero
  rw [← subtract_definition, left_distributive, ← h,
    ← negate_multiply_equal_multiply_negate, add_inverse]

theorem multiply_right_cancel {a b c : ℤ} (h : a * c = b * c) (c_nonzero : c ≠ 0) : a = b := by
  apply multiply_left_cancel (a := c)
  rw [multiply_commutative c a, multiply_commutative c b]
  exact h
  exact c_nonzero

theorem multiply_nonzero_of_nonzero {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  apply hb
  apply (multiply_left_cancel (a := a) . ha)
  rw [h, multiply_zero]

theorem nonzero_of_multiply_nonzero {a b : ℤ} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  not_or.mp (mt multiply_equal_zero_of_equal_zero h)

def ofNatural (n : ℕ) : ℤ :=
  Quotient.mk instanceSetoidIntegerEquivalent (n, 0)

instance : Coe Natural Integer := ⟨ofNatural⟩

theorem ofNatural_add (n m : ℕ) : ofNatural (n + m) = ofNatural n + ofNatural m := rfl

theorem ofNatural_multiply (n m : ℕ) : ofNatural (n * m) = ofNatural n * ofNatural m := by
  unfold ofNatural
  apply Quotient.sound
  show (n * m) + (n * 0 + 0 * m) = (n * m + 0 * 0) + 0
  simp [Natural.add_zero, Natural.zero_add, Natural.multiply_zero, Natural.zero_multiply]

theorem ofNatural_injective : Injective ofNatural := by
  intro a b h
  rw [← Natural.add_zero a, Quotient.exact h, Natural.add_zero]

theorem ofNatural_zero : ofNatural 0 = (0 : ℤ) := rfl

def LessEqual (a b : ℤ) : Prop := ∃ (n : ℕ), a + ↑n = b

instance : LE Integer where
  le := LessEqual

theorem less_equal_definition : (a ≤ b) = LessEqual a b := rfl

theorem LessEqual.reflexive : Reflexive LessEqual :=
  λ _ => Exists.intro 0 (add_zero _)

theorem LessEqual.antisymmetric : AntiSymmetric LessEqual := by
  intro a b ⟨n, hn⟩ ⟨m, hm⟩
  suffices m = 0 ∧ n = 0
  by rw [← add_zero a, ← ofNatural_zero, ← this.right, hn]
  apply Natural.equal_zero_of_add_equal_zero
  apply ofNatural_injective
  apply add_left_cancel (a := b)
  rw [ofNatural_add, ← add_associative, hm, hn, ofNatural_zero, add_zero]

theorem LessEqual.transitive : Transitive LessEqual := by
  intro a b c ⟨n, (ha : a + ↑n = b)⟩ ⟨m, (hb : b + ↑m = c)⟩
  apply Exists.intro ↑(n + m)
  rw [ofNatural_add, ← add_associative, ha, hb]

theorem less_equal_of_subtract_nonnegative {a b : ℤ} : 0 ≤ b - a → a ≤ b := by
  intro ⟨n, (h : 0 + ↑n = b - a)⟩
  apply Exists.intro n
  rw [add_commutative a ↑n, ← zero_add (↑n + a), ← add_associative, h,
    ← subtract_definition, add_associative, add_inverse_left, add_zero]

theorem subtract_nonnegative_of_less_equal {a b : ℤ} : a ≤ b → 0 ≤ b - a := by
  intro ⟨n, (h : a + ↑n = b)⟩
  apply Exists.intro n
  rw [← add_inverse a, add_right_commutative, h, subtract_definition]

theorem nonnegative_of_negative_less_equal_positive {n m : ℕ} : m ≤ n → (0 : ℤ) ≤ ⟦(n, m)⟧ := by
  intro ⟨a, (ha : m + a = n)⟩
  apply Exists.intro a
  apply Quotient.sound
  show (0 + a) + m = n + 0
  simp [Natural.add_zero, Natural.add_commutative, ha]

theorem negative_less_equal_positive_of_nonnegative {n m : ℕ} : (0 : ℤ) ≤ ⟦(n, m)⟧ → m ≤ n := by
  intro ⟨a, (ha : (0 : ℤ) + ↑a = ⟦(n, m)⟧)⟩
  have : (0 + a) + m = n + (0 + 0) := Quotient.exact ha
  simp [Natural.zero_add, Natural.add_commutative] at this
  exact (Exists.intro a this)

instance decideNonNegative (a : ℤ) : Decidable (0 ≤ a) :=
  Quotient.recOnSubsingleton a
  λ ((n, m) : ℕ × ℕ) =>
  if h : m ≤ n then
    isTrue (nonnegative_of_negative_less_equal_positive h)
  else
    isFalse (mt negative_less_equal_positive_of_nonnegative h)

instance decideLessEqual (a b : ℤ) : Decidable (a ≤ b) :=
  if h : 0 ≤ b - a then
    isTrue (less_equal_of_subtract_nonnegative h)
  else
    isFalse (mt subtract_nonnegative_of_less_equal h)

theorem LessEqual.strongly_connected : StronglyConnected LessEqual :=
  have lift_less_equal {n m k l : ℕ} : n + l ≤ k + m → LessEqual ⟦(n, m)⟧ ⟦(k, l)⟧ := by
  { intro ⟨a, (ha : (n + l) + a = k + m)⟩
    apply Exists.intro a
    apply Quotient.sound
    simp
    show (n + a) + l = k + m
    rw [Natural.add_right_commutative, ha] }
  Quotient.ind₂ λ (p, q) (s, t) =>
  Or.implies lift_less_equal lift_less_equal (Natural.LessEqual.strongly_connected (p + t) (s + q))

instance totalOrder : DecidableTotalOrder Integer where
  less_equal_reflexive := LessEqual.reflexive
  less_equal_antisymmetric := LessEqual.antisymmetric
  less_equal_transitive := LessEqual.transitive
  less_equal_strongly_connected := LessEqual.strongly_connected
  decideEqual := decideEqual
  decideLessEqual := decideLessEqual

theorem ofNatural_nonnegative (n : ℕ) : (0 : ℤ) ≤ ↑n :=
  Exists.intro n (zero_add n)
  
theorem ofNatural_successor_positive (n : ℕ) : (0 : ℤ) < ↑(successor n) := by
  match equal_or_less_than_of_less_equal (ofNatural_nonnegative (successor n)) with
  | Or.inl h =>
    have : 0 + 0 = successor n + 0 := Quotient.exact h
    simp [add_zero] at this
    exact absurd this.symm (Natural.successor_not_equal_zero n)
  | Or.inr h =>
    exact h

theorem equal_ofNatural_of_nonnegative : ∀ {a : ℤ}, 0 ≤ a → ∃ n : ℕ, ↑n = a := by
  apply Quotient.ind
  intro (n, m) ⟨a, ha⟩
  simp [zero_add] at ha
  exact Exists.intro a ha

abbrev NonNegativeInteger := {a : ℤ // 0 ≤ a}
abbrev PositiveInteger := {a : ℤ // 0 < a}
abbrev NonZeroInteger := {a : ℤ // a ≠ 0}
abbrev NegativeInteger := {a : ℤ // a < 0}
abbrev NonPositiveInteger := {a : ℤ // a ≤ 0}

notation "ℤ≥0" => NonNegativeInteger
notation "ℤ>0" => PositiveInteger
notation "ℤ≠0" => NonZeroInteger
notation "ℤ<0" => NegativeInteger
notation "ℤ≤0" => NonPositiveInteger

theorem add_left_monotone (a : ℤ) : Monotone (a + .) := by
  intro b c h
  let ⟨n, hn⟩ := h
  apply Exists.intro n
  rw [add_associative, hn]

theorem add_right_monotone (c : ℤ) : Monotone (. + c) := by
  intro a b h
  simp
  rw [add_commutative a c, add_commutative b c]
  exact add_left_monotone c h

theorem less_equal_of_add_less_equal_left {a b c : ℤ} (h : a + b ≤ a + c) : b ≤ c := by
  have := add_left_monotone (-a) h
  simp [negate_add_cancel_left] at this
  exact this

theorem less_equal_of_add_less_equal_right {a b c : ℤ} (h : a + c ≤ b + c) : a ≤ b := by
  rw [add_commutative a c, add_commutative b c] at h
  exact less_equal_of_add_less_equal_left h

theorem add_less_equal_add {a b c d : ℤ} (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d :=
  less_equal_transitive (add_right_monotone b hac) (add_left_monotone c hbd)

theorem less_equal_add_of_nonnegative_left {a b : ℤ} (h : 0 ≤ b) : a ≤ b + a := by
  have := add_less_equal_add h (less_equal_reflexive a)
  rw [zero_add] at this
  exact this

theorem less_equal_add_of_nonnegative_right {a b : ℤ} (h : 0 ≤ b) : a ≤ a + b := by
  rw [add_commutative a b]
  exact less_equal_add_of_nonnegative_left h
  
theorem less_equal_of_subtract_nonpositive {a b : ℤ} (h : a - b ≤ 0) : a ≤ b := by
  have := add_right_monotone b h
  simp [zero_add] at this
  rw [← subtract_definition, negate_add_cancel_right] at this
  exact this

theorem subtract_nonpositive_of_less_equal {a b : ℤ} (h : a ≤ b) : a - b ≤ 0 := by
  have := add_right_monotone (-b) h
  simp [add_inverse] at this
  exact this
  
theorem negate_antitone : Antitone negate := by
  intro a b h
  have ha := add_right_monotone (-a) h
  simp [add_inverse, add_commutative] at ha
  have hb := add_right_monotone (-b) ha
  simp [zero_add] at hb
  rw [add_right_commutative, add_inverse, zero_add] at hb
  exact hb

theorem less_equal_of_negate_less_equal_negate {a b : ℤ} (h : -b ≤ -a) : a ≤ b :=
  suffices - -a ≤ - -b by simp at this; exact this
  negate_antitone h
  
theorem multiply_nonnegative_left_monotone {a : ℤ} (ha : 0 ≤ a) : Monotone (a * .) := by
  intro b c h
  let ⟨n, hn⟩ := h
  let ⟨m, hm⟩ := ha
  rw [zero_add] at hm
  apply Exists.intro ↑(m * n)
  rw [ofNatural_multiply, hm, ← left_distributive, hn]
  
theorem multiply_nonnegative_right_monotone {c : ℤ} (hc : 0 ≤ c) : Monotone (. * c) := by
  unfold Monotone
  intro a b h
  simp
  rw [multiply_commutative a c, multiply_commutative b c]
  exact multiply_nonnegative_left_monotone hc h

theorem multiply_nonnegative {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  let ⟨n, hn⟩ := equal_ofNatural_of_nonnegative ha
  let ⟨m, hm⟩ := equal_ofNatural_of_nonnegative hb
  apply Exists.intro ↑(n * m)
  rw [zero_add, ofNatural_multiply, hn, hm]
  
theorem multiply_nonpositive {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  have := multiply_nonnegative (negate_antitone ha) (negate_antitone hb)
  rw [negate_definition, negate_definition, ← negate_multiply_equal_multiply_negate, ← negate_multiply_equal_negate_multiply, negate_negate] at this
  exact this

theorem multiply_nonpositive_of_nonnegative_of_nonpositive {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  rw [← multiply_zero a]
  exact multiply_nonnegative_left_monotone ha hb

theorem multiply_nonpositive_of_nonpositive_of_nonnegative {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  rw [← zero_multiply b]
  exact multiply_nonnegative_right_monotone hb ha
  
-- Tricky: We only require that c is nonnegative, a is totally cool to
-- be negative because that will make a*b negative which preserves
-- order
theorem multiply_less_equal_multiply {a b c d : ℤ} (hac : a ≤ c) (hbd : b ≤ d) 
    (hb : 0 ≤ b) (hc : 0 ≤ c) : a * b ≤ c * d :=
  less_equal_transitive
  (multiply_nonnegative_right_monotone hb hac)
  (multiply_nonnegative_left_monotone hc hbd)
  
theorem multiply_nonpositive_left_antitone {a : ℤ} (ha : a ≤ 0) : Antitone (a * .) := by
  intro b c h
  have := multiply_nonnegative_left_monotone (negate_antitone ha) h
  simp at this
  rw [← negate_multiply_equal_negate_multiply, ← negate_multiply_equal_negate_multiply] at this
  exact less_equal_of_negate_less_equal_negate this

theorem multiply_nonpositive_right_antitone {c : ℤ} (hc : c ≤ 0) : Antitone (. * c) := by
  intro a b h
  simp
  rw [multiply_commutative a c, multiply_commutative b c]
  exact multiply_nonpositive_left_antitone hc h
  
theorem equal_add_positive_of_less_than {a b : ℤ} (h : a < b) :
    ∃ (n : ℕ), n ≠ 0 ∧ a + ↑n = b := by
  let ⟨n, hab⟩ := less_equal_of_less_than h
  have n_nonzero : n ≠ 0 := by
  { intro  hn
    rw [hn, ofNatural_zero, add_zero] at hab
    exact absurd hab (not_equal_of_less_than h) }
  apply Exists.intro n (And.intro n_nonzero hab)

theorem less_than_of_equal_add_positive {a b : ℤ} {n : ℕ} : n ≠ 0 → a + ↑n = b → a < b := by
  intro n_nonzero hab
  apply less_than_of_less_equal_of_not_equal
  . exact Exists.intro n hab
  . intro hab'
    have := congrArg (-b + .) (hab' ▸ hab)
    simp [negate_add_cancel_left, add_inverse_left] at this
    exact absurd (ofNatural_injective this) n_nonzero

theorem less_than_equivalent_add_one_less_equal {a b : ℤ} : a < b ↔ a + 1 ≤ b := by
  have h1 : ofNatural 1 = 1 := rfl
  constructor
  . intro h
    have ⟨n, hn, hab⟩ := equal_add_positive_of_less_than h
    have ⟨m, hm, _⟩ := Natural.unique_predecessor_of_positive hn
    simp at hm
    have hs : successor m = 1 + m := rfl
    rw [← hm, hs, Natural.add_commutative, ofNatural_add, h1, add_commutative _ 1, ← add_associative] at hab
    exact Exists.intro m hab
  . intro ⟨n, hn⟩
    have hs : 1 + n = successor n := rfl
    rw [← h1, add_associative, ← ofNatural_add, hs] at hn
    exact less_than_of_equal_add_positive (Natural.successor_not_equal_zero n) hn
    
theorem equal_ofNatural_positive_of_positive {a : ℤ} (h : 0 < a) : 
    ∃ n : ℕ, n ≠ 0 ∧ ↑n = a := 
  equal_add_positive_of_less_than h

theorem add_left_strict_monotone (a : ℤ) : StrictMonotone (a + .) := by
  intro b c h
  let ⟨hbc, hcb⟩ := less_than_equivalent_less_equal_not_less_equal.mp h
  apply less_than_equivalent_less_equal_not_less_equal.mpr
  apply And.intro
  . exact add_left_monotone a hbc
  . intro h'
    have : c ≤ b := (less_equal_of_add_less_equal_left h')
    exact absurd this hcb
  
theorem add_right_strict_monotone (c : ℤ) : StrictMonotone (. + c) := by
  intro a b h
  simp
  rw [add_commutative a c, add_commutative b c]
  exact add_left_strict_monotone c h

theorem less_than_of_add_less_than_left {a b c : ℤ} (h : a + b < a + c) : b < c := by
  have := add_left_strict_monotone (-a) h
  simp [negate_add_cancel_left] at this
  exact this

theorem less_than_of_add_less_than_right {a b c : ℤ} (h : a + c < b + c) : a < b := by
  rw [add_commutative a c, add_commutative b c] at h
  exact less_than_of_add_less_than_left h
  
theorem add_less_than_add {a b c d : ℤ} (hac : a < c) (hbd : b < d) : a + b < c + d :=
  less_than_transitive (add_right_strict_monotone b hac) (add_left_strict_monotone c hbd)

theorem less_than_add_of_nonnegative_left {a b : ℤ} (h : 0 < b) : a < b + a := by
  have := add_right_strict_monotone a h
  simp [zero_add] at this
  exact this

theorem less_than_add_of_nonnegative_right {a b : ℤ} (h : 0 < b) : a < a + b := by
  rw [add_commutative a b]
  exact less_than_add_of_nonnegative_left h
  
theorem less_than_of_subtract_positive {a b : ℤ} : 0 < b - a → a < b := by
  intro h
  have := add_right_strict_monotone a h
  simp [zero_add, ← subtract_definition, negate_add_cancel_right] at this
  exact this

theorem subtract_positive_of_less_than {a b : ℤ} : a < b → 0 < b - a := by
  intro h
  have := add_right_strict_monotone (-a) h
  simp [add_inverse] at this
  exact this
    
theorem less_than_of_subtract_negative {a b : ℤ} (h : a - b < 0) : a < b := by
  have := add_right_strict_monotone b h
  simp at this
  rw [zero_add, ← subtract_definition, negate_add_cancel_right] at this
  exact this

theorem subtract_negative_of_less_than {a b : ℤ} (h : a < b) : a - b < 0 := by
  have := add_right_strict_monotone (-b) h
  simp [add_inverse] at this
  exact this

theorem negate_strict_antitone : StrictAntitone negate := by
  intro a b h
  have ha := add_left_strict_monotone (-b) h
  simp [add_inverse_left] at ha
  have hb := add_right_strict_monotone (-a) ha
  simp [zero_add, add_associative, add_inverse, add_zero] at hb
  exact hb

theorem less_than_of_negate_less_than_negate {a b : ℤ} (h : -b < -a) : a < b :=
  suffices - -a < - - b by simp at this; exact this
  negate_strict_antitone h

theorem multiply_positive_left_strict_monotone {a : ℤ} (ha : 0 < a) : StrictMonotone (a * .) := by
  intro b c h
  let ⟨n, hn, hbc⟩ := equal_add_positive_of_less_than h
  let ⟨m, hm, ha⟩ := equal_ofNatural_positive_of_positive ha
  apply less_than_of_equal_add_positive
  . exact Natural.multiply_positive_of_positive hn hm
  . rw [ofNatural_multiply, ha, multiply_commutative _ a, ← left_distributive]
    exact congrArg (a * .) hbc
  
theorem multiply_positive_right_strict_monotone {c : ℤ} (hc : 0 < c) : StrictMonotone (. * c) := by
  intro a b h
  simp [multiply_commutative a c, multiply_commutative b c]
  exact multiply_positive_left_strict_monotone hc h

theorem multiply_positive {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  let ⟨n, hn, ha⟩ := equal_ofNatural_positive_of_positive ha
  let ⟨m, hm, hb⟩ := equal_ofNatural_positive_of_positive hb
  -- TODO: Need to make a nonzero theorem, also rename integer one to nonzero
  apply less_than_of_equal_add_positive 
  . exact (Natural.multiply_positive_of_positive hn hm)
  . rw [zero_add, ofNatural_multiply, ha, hb]

theorem multiply_negative {a b : ℤ} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  let ⟨n, hn, ha⟩ := equal_ofNatural_positive_of_positive (negate_strict_antitone ha)
  let ⟨m, hm, hb⟩ := equal_ofNatural_positive_of_positive (negate_strict_antitone hb)
  apply less_than_of_equal_add_positive
  . exact (Natural.multiply_positive_of_positive hn hm)
  . rw [zero_add, ofNatural_multiply, ha, hb, negate_definition, negate_definition, 
       ← negate_multiply_equal_negate_multiply, ← negate_multiply_equal_multiply_negate, negate_negate]

theorem multiply_negative_of_positive_of_negative {a b : ℤ} (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  rw [← multiply_zero a]
  exact multiply_positive_left_strict_monotone ha hb

theorem multiply_negative_of_negative_of_positive {a b : ℤ} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  rw [← zero_multiply b]
  exact multiply_positive_right_strict_monotone hb ha

theorem multiply_less_than_multiply {a b c d : ℤ} (hac : a < c) (hbd : b < d) 
    (hb : 0 < b) (hc : 0 < c) : a * b < c * d :=
  less_than_transitive
  (multiply_positive_right_strict_monotone hb hac)
  (multiply_positive_left_strict_monotone hc hbd)
  
theorem multiply_negative_left_strict_antitone {a : ℤ} (ha : a < 0) : StrictAntitone (a * .) := by
  intro b c h
  have := multiply_positive_left_strict_monotone (negate_strict_antitone ha) h
  simp [← negate_multiply_equal_negate_multiply, ← negate_multiply_equal_negate_multiply] at this
  exact less_than_of_negate_less_than_negate this
  
theorem multiply_negative_right_strict_antitone {c : ℤ} (hc : c < 0) : StrictAntitone (. * c) := by
  intro a b h
  simp [multiply_commutative a c, multiply_commutative b c]
  exact multiply_negative_left_strict_antitone hc h
  
-- TODO: The names are wrong, prove positive_left_* version, so switch
theorem positive_right_of_multiply_positive_of_positive_left {a b : ℤ} (h : 0 < a * b) (ha : 0 < a) : 0 < b := by
  match less_than_trichotomous 0 b with
  | Or.inl h_less => exact h_less
  | Or.inr (Or.inl h_equal) =>
    rw [← h_equal, multiply_zero] at h
    exact absurd h (less_than_irreflexive 0)
  | Or.inr (Or.inr h_greater) =>
    have := multiply_negative_of_positive_of_negative ha h_greater
    exact absurd (less_than_transitive this h) (less_than_irreflexive (a * b))
    
theorem positive_left_of_multiply_positive_of_positive_right {a b : ℤ} (h : 0 < a * b) (hb : 0 < b) : 0 < a := by
  rw [multiply_commutative] at h
  exact positive_right_of_multiply_positive_of_positive_left h hb
  
theorem negative_left_of_multiply_negative_of_positive_right {a b : ℤ} (h : a * b < 0) (hb : 0 < b) : a < 0 := by
  match less_than_trichotomous 0 a with
  | Or.inl a_positive =>
    have := multiply_positive a_positive hb
    exact absurd (less_than_transitive this h) (less_than_irreflexive 0)
  | Or.inr (Or.inl a_zero) =>
    rw [← a_zero, zero_multiply] at h
    exact absurd h (less_than_irreflexive 0)
  | Or.inr (Or.inr a_negative) => exact a_negative
  
theorem negative_right_of_multiply_negative_of_positive_left {a b : ℤ} (h : a * b < 0) (ha : 0 < a) : b < 0 := by
  rw [multiply_commutative] at h
  exact negative_left_of_multiply_negative_of_positive_right h ha

theorem less_than_multiply_cancel_left_of_positive {a b c : ℤ} (h : a * b < a * c) (ha : 0 < a) : b < c := by
  -- If we subtract a*b from both sides and distribute
  -- (undistribute?), we have a * (c - b). We proved earlier
  -- (specifically because I realized that I needed it to prove this
  -- one), that if we have a * b > 0 and a > 0, then b > 0. Applying
  -- this gives c - b > 0, and then we apply the theorem which gives b
  -- < c.  This was a good example of having no clue what to do, I
  -- tried to appeal to the existence of the natural number and even
  -- do induction on it, but I needed to develop the simpler theorem
  -- about sharing signs first and then apply it here.
  have := add_right_strict_monotone (-(a*b)) h
  simp [multiply_zero, add_inverse, negate_multiply_equal_multiply_negate, ← left_distributive] at this
  exact less_than_of_subtract_positive (positive_right_of_multiply_positive_of_positive_left this ha)
  
theorem less_than_multiply_cancel_right_of_positive {a b c : ℤ} (h : a * c < b * c) (hc : 0 < c) : a < b := by
  rw [multiply_commutative a c, multiply_commutative b c] at h
  exact less_than_multiply_cancel_left_of_positive h hc
  
theorem less_equal_multiply_cancel_left_of_positive {a b c : ℤ} (h : a * b ≤ a * c) (ha : 0 < a) : b ≤ c :=
  match less_than_or_equal_of_less_equal h with
  | Or.inl h_less => less_equal_of_less_than <|
    less_than_multiply_cancel_left_of_positive h_less ha
  | Or.inr h_equal => less_equal_of_equal <|
    multiply_left_cancel h_equal (not_equal_of_less_than ha).symm

theorem less_equal_multiply_cancel_right_of_positive {a b c : ℤ} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b := by
  rw [multiply_commutative a c, multiply_commutative b c] at h
  exact less_equal_multiply_cancel_left_of_positive h hc

theorem add_less_than_of_less_than_of_less_equal {a b c d : ℤ} (hac : a < c) (hbd : b ≤ d) : a + b < c + d :=
  less_than_of_less_than_of_less_equal (add_right_strict_monotone b hac) (add_left_monotone c hbd)

theorem add_less_than_of_less_equal_of_less_than {a b c d : ℤ} (hac : a ≤ c) (hbd : b < d) : a + b < c + d :=
  less_than_of_less_equal_of_less_than (add_right_monotone b hac) (add_left_strict_monotone c hbd)

namespace NonNegativeInteger

def preToNatural' : ℕ × ℕ → Option ℕ
  | (n, m) => if n ≥ m then some (Natural.distance n m) else none

@[simp]
theorem preToNatural_none (x : ℕ × ℕ) (h : x.1 < x.2) : preToNatural' x = none := by
  have := not_less_equal_of_greater_than h
  simp [preToNatural', not_less_equal_of_greater_than h]

@[simp]
theorem preToNatural_some (x : ℕ × ℕ) (h : x.1 ≥ x.2) : preToNatural' x = some (Natural.distance x.1 x.2) := by
  simp [preToNatural', h]

def toNatural' : ℤ → Option ℕ :=
  Quotient.lift preToNatural' <| by
  intro (n, m) (k, l) (h : n + l = k + m)
  cases Decidable.em (m ≤ n)
  <;> cases Decidable.em (l ≤ k)
  <;> simp_all [preToNatural', preToNatural_none, preToNatural_some]
  case inl.inl hnm hkl =>
    rw [Natural.add_commutative k m] at h
    exact Natural.distance_equal_of_add_equal h
  case inl.inr hnm hkl =>
    rw [Natural.add_commutative k m] at h
    have := Natural.right_greater_equal_of_add_left_less_equal h.symm hnm
    exact absurd this hkl
  case inr.inl hnm hkl =>
    rw [Natural.add_commutative n l] at h
    have := Natural.right_greater_equal_of_add_left_less_equal h hkl
    exact absurd this hnm

def toNatural : ℤ≥0 → ℕ
  | (⟨a, a_nonnegative⟩) =>
    Option.get (toNatural' a) <| by
    have ⟨n, hn⟩ := equal_ofNatural_of_nonnegative a_nonnegative
    rw [toNatural', ← hn, ofNatural, Quotient.lift_construct, preToNatural']
    simp [Natural.zero_less_equal, subtract_zero, ite_true, Option.isSome]

def fromNatural (n : ℕ) : ℤ≥0 :=
  ⟨n, ofNatural_nonnegative n⟩

theorem fromNatural_toNatural_left_inverse : LeftInverse toNatural fromNatural := by
  intro n
  simp [fromNatural, ofNatural, toNatural, toNatural', preToNatural', Natural.distance_zero_left]
  
theorem fromNatural_toNatural_right_inverse : RightInverse toNatural fromNatural := by
  intro ⟨a, b, h⟩
  rw [zero_add, ofNatural] at h
  subst h
  simp [toNatural, toNatural', preToNatural', fromNatural, ofNatural, Natural.distance_zero_left]

theorem toNatural_add (a b : ℤ≥0) : 
    let hab : 0 ≤ a.val + b.val := add_less_equal_add a.property b.property
    toNatural a + toNatural b = toNatural ⟨a.val + b.val, hab⟩ := by
  let ⟨n, hn⟩ := equal_ofNatural_of_nonnegative a.property
  let ⟨m, hm⟩ := equal_ofNatural_of_nonnegative b.property
  simp [toNatural, toNatural', ← hn, ← hm, ← ofNatural_add]
  simp [ofNatural, Natural.distance_zero_left]

theorem toNatural_multiply (a b : ℤ≥0) :
    let hab : 0 ≤ a.val * b.val := multiply_nonnegative a.property b.property
    toNatural a * toNatural b = toNatural ⟨a.val * b.val, hab⟩ := by
  let ⟨n, hn⟩ := equal_ofNatural_of_nonnegative a.property
  let ⟨m, hm⟩ := equal_ofNatural_of_nonnegative b.property
  simp [toNatural, toNatural', ← hn, ← hm, ← ofNatural_multiply]
  simp [ofNatural, Natural.distance_zero_left]

theorem toNatural_positive (a : ℤ) (ha : 0 < a) : 0 < toNatural ⟨a, less_equal_of_less_than <| ha⟩ := by
  apply And.intro
  . exact Natural.zero_less_equal _
  . intro h
    have := congrArg Integer.NonNegativeInteger.fromNatural (Natural.equal_zero_of_less_equal_zero h)
    have rw := fromNatural_toNatural_right_inverse ⟨a, less_equal_of_less_than <| ha⟩
    simp at rw
    simp [rw] at this
    simp [fromNatural, ofNatural_zero] at this
    exact absurd this (not_equal_of_less_than ha).symm

end NonNegativeInteger

namespace NonPositiveInteger

def toNatural : ℤ≤0 → ℕ
  | ⟨a, ha⟩ => NonNegativeInteger.toNatural ⟨-a, negate_antitone ha⟩

def fromNatural (n : ℕ) : ℤ≤0 :=
  let ⟨a, ha⟩ := NonNegativeInteger.fromNatural n
  ⟨-a, negate_antitone ha⟩
  
theorem fromNatural_toNatural_left_inverse : LeftInverse toNatural fromNatural := 
  NonNegativeInteger.fromNatural_toNatural_left_inverse

theorem fromNatural_toNatural_right_inverse : RightInverse toNatural fromNatural := by
  intro ⟨a, ha⟩
  unfold toNatural fromNatural
  have := NonNegativeInteger.fromNatural_toNatural_right_inverse ⟨-a, negate_antitone ha⟩
  simp at this
  simp [this]
  
theorem toNatural_add (a b : ℤ≤0) : 
    let hab : a.val + b.val ≤ 0 := add_less_equal_add a.property b.property
    toNatural a + toNatural b = toNatural ⟨a.val + b.val, hab⟩ := by
  simp [toNatural, NonNegativeInteger.toNatural_add, negate_add]

theorem toNatural_multiply (a b : ℤ≤0) :
    let hab : 0 ≤ a.val * b.val := multiply_nonpositive a.property b.property
    toNatural a * toNatural b = Integer.NonNegativeInteger.toNatural ⟨a.val * b.val, hab⟩ := by
  simp [toNatural]
  have := Integer.NonNegativeInteger.toNatural_multiply 
    ⟨-a.val, negate_antitone a.property⟩ ⟨-b.val, negate_antitone b.property⟩
  simp at this
  conv at this in (-a.val * -b.val) => 
    rw [← negate_multiply_equal_multiply_negate, ← negate_multiply_equal_negate_multiply, negate_negate]
  exact this

end NonPositiveInteger

instance instanceRepr : Repr Integer where
  reprPrec a p :=
    if h : 0 ≤ a then
      let n := Integer.NonNegativeInteger.toNatural ⟨a, h⟩
      Natural.instanceRepr.reprPrec n p
    else
      let n := Integer.NonPositiveInteger.toNatural ⟨a, less_equal_of_not_greater_equal h⟩
      Repr.addAppParen ("-" ++ Natural.instanceRepr.reprPrec n p) p

-- TODO: Copied from rationals
def magnitude (a : ℤ) : ℤ := maximum a (-a)

macro:max atomic("|" noWs) a:term noWs "|" : term => `(magnitude $a)

theorem magnitude_negate (x : ℤ) : |-x| = |x| := by
  unfold magnitude 
  simp [negate_negate, join_commutative]

theorem magnitude_nonnegative (x : ℤ) : 0 ≤ |x| := by
  unfold magnitude
  match less_than_trichotomous 0 x with
  | Or.inl h => 
    exact less_equal_join_of_less_equal_left (-x) (less_equal_of_less_than h)
  | Or.inr (Or.inl h) =>
    have := less_equal_join_of_less_equal_left (0 : ℤ) (less_equal_reflexive 0)
    simp [← h, ← negate_zero, this]
  | Or.inr (Or.inr h) =>
    have := negate_antitone (less_equal_of_less_than h)
    simp [negate_definition, ← negate_zero] at this
    rw [maximum_join, join_commutative]
    exact less_equal_join_of_less_equal_left x this

theorem magnitude_zero : |0| = 0 := rfl

theorem zero_of_magnitude_value_zero {x : ℤ} (h : |x| = 0) : x = 0 := by
  rw [magnitude] at h
  match Decidable.em (x ≤ -x) with
  | Or.inl hx => 
    have := congrArg negate ((join_equal_right.mpr hx).symm.trans h)
    simp at this
    exact this
  | Or.inr hx => 
    exact (join_equal_left.mpr (greater_equal_of_not_less_equal hx)).symm.trans h

theorem magnitude_positive {x : ℤ} (h : x ≠ 0) : 0 < |x| :=
  match less_than_or_equal_of_less_equal (magnitude_nonnegative x) with
  | Or.inl hx => hx
  | Or.inr hx => absurd hx.symm (mt zero_of_magnitude_value_zero h)

theorem magnitude_equal_of_nonnegative {x : ℤ} (h : 0 ≤ x) : |x| = x :=
  join_equal_left.mpr (less_equal_transitive (negate_antitone h) h)

theorem magnitude_equal_negate_of_nonpositive {x : ℤ} (h : x ≤ 0) : |x| = -x :=
  join_equal_right.mpr (less_equal_transitive h (negate_antitone h))
  
theorem magnitude_equal_of_positive {x : ℤ} : 0 < x → |x| = x :=
  magnitude_equal_of_nonnegative ∘ less_equal_of_less_than

theorem magnitude_equal_negate_of_negative {x : ℤ} : x < 0 → |x| = -x :=
  magnitude_equal_negate_of_nonpositive ∘ less_equal_of_less_than

theorem less_equal_magnitude (x : ℤ) : x ≤ |x| :=
  less_equal_join_left x (-x)

theorem negate_magnitude_less_equal (x : ℤ) : -|x| ≤ x := by
  have := negate_antitone (less_equal_magnitude (-x))
  simp [magnitude_negate] at this
  exact this
  
theorem magnitude_less_equal_equivalent_negate_less_equal_self {x y : ℤ} :
    -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  apply Iff.intro
  . intro h
    rw [magnitude]
    have := negate_antitone h.left
    simp at this
    exact join_less_equal_equivalent.mpr (And.intro h.right this)
  . intro h
    simp [magnitude] at h
    have ⟨hl, hr⟩ := join_less_equal_equivalent.mp h
    have hr' := negate_antitone hr
    simp [negate_negate] at hr'
    exact ⟨hr', hl⟩

theorem magnitude_less_equal_of_negate_less_equal {x y : ℤ} : -y ≤ x → x ≤ y → |x| ≤ y :=
  λ hyx hxy =>
  magnitude_less_equal_equivalent_negate_less_equal_self.mp (And.intro hyx hxy)

theorem negate_less_equal_of_magnitude_less_equal {x y : ℤ} : |x| ≤ y → -y ≤ x ∧ x ≤ y :=
  magnitude_less_equal_equivalent_negate_less_equal_self.mpr
  
theorem magnitude_multiply_equal_multiply_magnitude (x y : ℤ) : |x * y| = |x| * |y| := by
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

def divideWithRemainder' (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) : 
    Σ' qr : ℤ × ℤ, 
    let (q, r) := qr
    a = q*b + r ∧ 0 ≤ r ∧ r < b :=
  if h : b ≤ a then
    have hba := subtract_nonnegative_of_less_equal h
    have : NonNegativeInteger.toNatural ⟨a - b, hba⟩ < NonNegativeInteger.toNatural ⟨a, ha⟩ := by
      let j := NonNegativeInteger.toNatural ⟨b, less_equal_of_less_than <| hb⟩
      apply @Natural.less_than_of_equal_add_positive _ _ j
      . have := NonNegativeInteger.toNatural_positive b hb
        have hj : j = NonNegativeInteger.toNatural ⟨b, less_equal_of_less_than <| hb⟩ := rfl
        rw [← hj] at this
        exact Ne.symm <| not_equal_of_less_than <| this
      . simp [j, NonNegativeInteger.toNatural_add, ← subtract_definition, add_associative, add_inverse_left, add_zero]
    let ⟨(q', r), ⟨hab', hr1, hr2⟩⟩ := divideWithRemainder' (a - b) b hba hb
    have hab : a = (q' + 1) * b + r := by
      rw [right_distributive, one_multiply]
      have := congrArg (. + b) hab'
      simp [← subtract_definition, add_associative, add_inverse_left, add_zero, add_commutative r b] at this
      simp [← add_associative] at this
      exact this
    ⟨(q' + 1, r), And.intro hab (And.intro hr1 hr2)⟩
  else
    ⟨(0, a), And.intro (by simp [zero_multiply, zero_add]) (And.intro ha (less_than_of_not_greater_equal h))⟩
termination_by NonNegativeInteger.toNatural ⟨a, ha⟩

def divideWithRemainder (a b : ℤ) (hb : b ≠ 0) :
    Σ' qr : ℤ × ℤ,
    let (q, r) := qr
    a = q * b + r ∧ 0 ≤ r ∧ r < |b| :=
  if h1 : 0 ≤ a ∧ 0 < b then
    let ⟨(q, r), ⟨hab, hr1, hr2'⟩⟩ := divideWithRemainder' a b h1.left h1.right
    have hr2 := by
      simp [magnitude_equal_of_nonnegative (less_equal_of_less_than h1.right), hr2']
    ⟨(q, r), ⟨hab, hr1, hr2⟩⟩
  else if h2 : 0 ≤ a ∧ b < 0 then
    let ⟨(q', r), ⟨hab', hr1, hr2'⟩⟩ := divideWithRemainder' a (-b) h2.left (negate_strict_antitone h2.right)
    have hab := by
      rw [← negate_multiply_equal_multiply_negate, negate_multiply_equal_negate_multiply] at hab'
      exact hab'
    have hr2 : r < |b| := by
      have g1 := less_equal_magnitude (-b)
      have g2 := magnitude_negate b
      rw [g2] at g1
      exact less_than_of_less_than_of_less_equal hr2' g1
    ⟨(-q', r), And.intro hab (And.intro hr1 hr2)⟩
  else if h3 : a ≤ 0 ∧ 0 < b then
    let ⟨(q', r'), ⟨hab', hr1', hr2'⟩⟩ := divideWithRemainder' (-a) b (negate_antitone h3.left) h3.right
    if hr' : r' = 0 then
      have hab := by
        simp [hr', add_zero] at hab'
        have := congrArg negate hab'
        rw [negate_definition, negate_negate a, negate_definition, negate_multiply_equal_negate_multiply] at this
        simp [add_zero]
        exact this
      ⟨(-q', 0), And.intro hab (And.intro (less_equal_reflexive _) (magnitude_positive hb))⟩
    else
      have hab : a = -(q' + 1) * b + (b - r') := by
        have hab'' := congrArg negate hab'
        simp [negate_add, negate_multiply_equal_negate_multiply] at hab''
        rw [negate_add, right_distributive, ← negate_multiply_equal_negate_multiply 1 b, one_multiply, 
          add_associative, ← subtract_definition, negate_add_cancel_left]
        exact hab''
      have hr1 := less_equal_of_less_than <| subtract_positive_of_less_than hr2'
      have hr2 := by
        rw [magnitude_equal_of_positive (less_than_of_less_equal_of_less_than hr1' hr2')]
        have hr'' := less_than_of_less_equal_of_not_equal hr1' (Ne.symm hr')
        have := add_less_than_of_less_equal_of_less_than (less_equal_reflexive b) (negate_strict_antitone hr'')
        simp [subtract_definition, subtract_zero] at this
        exact this
      ⟨(-(q' + 1), b - r'), And.intro hab (And.intro hr1 hr2)⟩
  else
    have ha : a ≤ 0 := by
      -- TODO: Kinda brute force much
      match (Decidable.not_and_iff_or_not _ _).mp h1, (Decidable.not_and_iff_or_not _ _).mp h2 with
      | Or.inl hl, Or.inl _ => exact less_equal_of_not_greater_equal hl
      | Or.inl hl, Or.inr _ => exact less_equal_of_not_greater_equal hl
      | Or.inr _, Or.inl hr => exact less_equal_of_not_greater_equal hr
      | Or.inr hl, Or.inr hr => exact absurd (less_than_of_less_equal_of_not_equal (less_equal_of_not_greater_than hl) hb) hr
    have hb : b < 0 := by
      match (Decidable.not_and_iff_or_not _ _).mp h2, (Decidable.not_and_iff_or_not _ _).mp h3 with
      | Or.inl _, Or.inl hr => exact absurd ha hr
      | Or.inl _, Or.inr hr => exact less_than_of_less_equal_of_not_equal (less_equal_of_not_greater_than hr) hb
      | Or.inr _, Or.inl hr => exact absurd ha hr
      | Or.inr hl, Or.inr hr => exact absurd (less_than_of_less_equal_of_not_equal (less_equal_of_not_greater_than hl) hb.symm) hr
    let ⟨(q', r'), ⟨hab', hr1', hr2'⟩⟩ := divideWithRemainder' (-a) (-b) (negate_antitone ha) (negate_strict_antitone hb)
    if hr' : r' = 0 then
      have hab := by
        simp [hr', add_zero] at hab'
        have := congrArg negate hab'
        rw [negate_definition, negate_negate a, negate_definition, negate_multiply_equal_negate_multiply] at this
        simp [← negate_multiply_equal_multiply_negate, ← negate_multiply_equal_negate_multiply] at this
        simp [add_zero]
        exact this
      ⟨(q', 0), And.intro hab (And.intro (less_equal_reflexive _) (magnitude_positive <| not_equal_of_less_than hb))⟩
    else
      have hab : a = (q' + 1) * b + (-b - r') := by
        have hab'' := congrArg negate hab'
        simp [negate_add, negate_multiply_equal_negate_multiply] at hab''
        simp [← negate_multiply_equal_multiply_negate, ← negate_multiply_equal_negate_multiply] at hab''
        rw [right_distributive, one_multiply, ← subtract_definition, add_associative, ← add_associative b, add_inverse, zero_add]
        exact hab''
      have hr1 := less_equal_of_less_than <| subtract_positive_of_less_than hr2'
      have hr2 := by
        have hb' := magnitude_equal_negate_of_negative hb
        rw [hb']
        have hr'' : 0 < r' := less_than_of_less_equal_of_not_equal hr1' (Ne.symm hr')
        have := add_less_than_of_less_equal_of_less_than (less_equal_reflexive (-b)) (negate_strict_antitone hr'')
        simp [← negate_zero, add_zero, subtract_definition] at this
        exact this
      ⟨(q' + 1, -b - r'), And.intro hab (And.intro hr1 hr2)⟩
    
theorem divideWithRemainder_unique {a b q r : ℤ} (hb : b ≠ 0)
    (h : a = q*b + r) (hr1 : 0 ≤ r) (hr2 : r < |b|) :
    ∀ (q' r' : ℤ), a = q'*b + r' → 0 ≤ r' → r' < |b| → (q' = q ∧ r' = r) := by
  intro q' r' h' hr1' hr2'
  have hh' := subtract_equal_zero_of_equal <| h'.symm.trans h
  rw [← subtract_definition, negate_add, add_associative, add_left_commutative r', ← add_associative, 
    negate_multiply_equal_negate_multiply, ← right_distributive, ← negate_negate (r' + -r), 
    subtract_definition, negate_add, negate_negate] at hh'
  have hh := equal_of_subtract_equal_zero hh'
  simp [subtract_definition, add_commutative] at hh
  if hq : q = q' then
    constructor
    . exact hq.symm
    . rw [subtract_equal_zero_of_equal hq.symm, zero_multiply] at hh
      exact (equal_of_subtract_equal_zero hh.symm).symm
  else
    have hqq' : q' - q ≠ 0 := mt equal_of_subtract_equal_zero (Ne.symm hq)
    have hm : |q' - q| * |b| = |r - r'| := by
      have := congrArg magnitude hh
      rw [magnitude_multiply_equal_multiply_magnitude] at this
      exact this
    have hl : |r - r'| < |b| := by
      match less_equal_strongly_connected r r' with
      | Or.inl hrr' =>
        have hrr'' := subtract_nonnegative_of_less_equal hrr'
        have : r' + (-r) < |b| + (-0) := add_less_than_of_less_than_of_less_equal hr2' (negate_antitone hr1)
        rw [subtract_definition, ← negate_zero, add_zero, ← magnitude_equal_of_nonnegative hrr'', 
          ← magnitude_negate, negate_subtract] at this
        exact this
      | Or.inr hrr' =>
        have hrr'' := subtract_nonnegative_of_less_equal hrr'
        have : r + (-r') < |b| + (-0) := add_less_than_of_less_than_of_less_equal hr2 (negate_antitone hr1')
        rw [subtract_definition, ← negate_zero, add_zero, ← magnitude_equal_of_nonnegative hrr''] at this
        exact this
    have hr : |b| ≤ |q' - q| * |b| := by
      have := less_than_equivalent_add_one_less_equal.mp (magnitude_positive hqq')
      simp [zero_add] at this
      have := multiply_less_equal_multiply this (less_equal_reflexive |b|) 
        (less_equal_of_less_than <| magnitude_positive hb) 
        (less_equal_transitive (by decide) this)
      rw [one_multiply] at this
      exact this
    rw [hm] at hr
    have : |b| < |b| := less_than_of_less_equal_of_less_than hr hl
    exact False.elim (less_than_irreflexive |b| this)

theorem divideWithRemainder'_unique {a b q r : ℤ} (_ : 0 ≤ a) (hb : 0 < b)
    (h : a = q*b + r) (hr1 : 0 ≤ r) (hr2 : r < b) :
    ∀ (q' r' : ℤ), a = q'*b + r' → 0 ≤ r' → r' < b → (q' = q ∧ r' = r) := by
  have := divideWithRemainder_unique (not_equal_of_less_than hb).symm h hr1 
  have hb := magnitude_equal_of_positive hb
  rw [hb] at this
  exact this hr2

def Divide (a b : ℤ) : Prop := ∃ q : ℤ, b = a * q

instance : Dvd ℤ where
  dvd := Divide

theorem divide_definition (a b : ℤ) : (a ∣ b) = Divide a b := rfl
 
theorem zero_divide (a : ℤ) : a ∣ 0 := Exists.intro 0 <| by
  rw [multiply_zero]

theorem divide_one (a : ℤ) : 1 ∣ a := Exists.intro a <| by
  rw [one_multiply]

theorem divide_negative_one (a : ℤ) : (-1) ∣ a := Exists.intro (-a) <| by
  rw [← negate_multiply_equal_multiply_negate, ← negate_multiply_equal_negate_multiply, negate_negate, one_multiply]

def Unit (a : ℤ) : Prop := a ∣ 1

theorem unit_one_or_negative_one {a : ℤ} : Unit a ↔ (a = 1 ∨ a = -1) := by
  constructor
  . intro ⟨q, hq⟩
    if ha : (a = 1 ∨ a = -1) then
      exact ha
    else
      have ha' := or_imply.mp ha
      simp at ha'
      if ha'' : a = 0 then
        rw [ha'', zero_multiply] at hq
        contradiction
      else if hq' : q = 0 then
        rw [hq', multiply_zero] at hq
        contradiction
      else
        have h : 1 = |a| * |q| := by
          rw [← @magnitude_equal_of_positive 1 (by decide), ← magnitude_multiply_equal_multiply_magnitude]
          exact congrArg magnitude hq
        have hn : 1 < |a| * |q| := by
          have ham : 1 < |a| := by
            apply less_than_of_less_equal_of_not_equal
            . exact less_than_equivalent_add_one_less_equal.mp <| magnitude_positive ha''
            . intro h
              simp [magnitude, maximum] at h
              if ha''' : a ≤ -a then
                simp [ha'''] at h
                have := congrArg (- .) h
                simp at this
                exact absurd this.symm ha'.right
              else
                simp [ha'''] at h
                exact absurd h.symm ha'.left
          have hqm := less_than_equivalent_add_one_less_equal.mp <| magnitude_positive hq'
          rw [zero_add] at hqm
          have := multiply_nonnegative_left_monotone (magnitude_nonnegative a) hqm
          simp [multiply_one] at this
          exact less_than_of_less_than_of_less_equal ham this
        exact absurd h (not_equal_of_less_than hn)
  . intro h
    match h with
    | Or.inl h => exact Exists.intro 1 <| by rw [h, one_multiply]
    | Or.inr h => exact Exists.intro (-1) <| by
      { rw [h, ← negate_multiply_equal_multiply_negate, ← negate_multiply_equal_negate_multiply, negate_negate, one_multiply] }
    
theorem negate_divide (a b : ℤ) : a ∣ b → -a ∣ b := by
  intro ⟨q, hq⟩
  apply Exists.intro (-q)
  rw [← negate_multiply_equal_multiply_negate, ← negate_multiply_equal_negate_multiply, negate_negate]
  exact hq

theorem divide_negate (a b : ℤ) : a ∣ b → a ∣ -b := by
  intro ⟨q, hq⟩
  apply Exists.intro (-q)
  rw [← negate_multiply_equal_multiply_negate]
  exact congrArg (- .) hq

theorem divide_antisymmetric_up_to_sign {a b : ℤ} : a ∣ b → b ∣ a → |a| = |b| := by
  intro ⟨p, hp⟩ ⟨q, hq⟩
  if hb' : b = 0 then
    simp [hb', zero_multiply] at hq
    simp [hb', hq]
  else
    rw [hq, multiply_associative] at hp
    rw (config := {occs := .pos [1]}) [← multiply_one b] at hp
    have hq' : q ∣ 1 := Exists.intro p (multiply_left_cancel hp hb')
    match unit_one_or_negative_one.mp hq' with
    | Or.inl hq' =>
      rw [hq', multiply_one] at hq
      exact congrArg magnitude hq
    | Or.inr hq' =>
      rw [hq', ← negate_multiply_equal_multiply_negate, multiply_one] at hq
      have := congrArg magnitude hq
      rw [magnitude_negate] at this
      exact this

theorem divide_equivalent_remainder_zero (a b : ℤ) (hb : b ≠ 0) : 
    let ⟨(_, r), _⟩ := divideWithRemainder a b hb
    b ∣ a ↔ r = 0 := by
  let ⟨(q, r), ⟨h, hr1, hr2⟩⟩ := divideWithRemainder a b hb
  constructor
  . intro ⟨p, hp⟩
    rw [← add_zero (b * p), multiply_commutative b p] at hp
    have ⟨_, hr⟩ := divideWithRemainder_unique hb h hr1 hr2 p 0 hp (less_equal_reflexive 0) (magnitude_positive hb)
    exact hr.symm
  . intro hr
    simp [hr, add_zero, multiply_commutative] at h
    exact Exists.intro q h

def DivideNonnegative (a b : ℤ≥0) : Prop := Divide a.val b.val

instance : Dvd ℤ≥0 where
  dvd := DivideNonnegative

theorem divide_reflexive : Reflexive Divide := by
  intro a
  apply Exists.intro 1
  rw [multiply_one]

theorem divide_antisymmetric : AntiSymmetric DivideNonnegative := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ hab hba
  have := divide_antisymmetric_up_to_sign hab hba
  simp [magnitude_equal_of_nonnegative, ha, hb] at this
  simp [this]

theorem divide_transitive : Transitive Divide := by
  intro a b c ⟨p, hp⟩ ⟨q, hq⟩
  apply Exists.intro (p * q)
  rw [hp, multiply_associative] at hq
  exact hq

instance instanceDividePreorder : Preorder ℤ where
  le := Divide
  less_equal_reflexive := divide_reflexive
  less_equal_transitive := divide_transitive
  lt a b := Divide a b ∧ ¬Divide b a

instance instanceDivideNonnegativePartialOrder : PartialOrder ℤ≥0 where
  le := DivideNonnegative
  less_equal_reflexive a := divide_reflexive a
  less_equal_transitive hab hbc := divide_transitive hab hbc
  less_equal_antisymmetric := divide_antisymmetric

def GreatestCommonDivisor (a b d : ℤ) := @Meet ℤ instanceDividePreorder a b d

def LeastCommonMultiple (a b m : ℤ) := @Join ℤ instanceDividePreorder a b m

theorem gcd_unique_up_to_sign {a b c d : ℤ} : GreatestCommonDivisor a b c → GreatestCommonDivisor a b d → |c| = |d| := by
  intro ⟨hca, hcb, hc⟩ ⟨hda, hdb, hd⟩
  exact divide_antisymmetric_up_to_sign (hd hca hcb) (hc hda hdb)

theorem foo {a b q r c d : ℤ} : a = q*b + r → 
    0 ≤ c → GreatestCommonDivisor a b c → 
    0 ≤ d → GreatestCommonDivisor b r d → 
    c = d := by
  intro hab hc ⟨⟨s, hs⟩, ⟨t, ht⟩, hc'⟩ hd ⟨hda, hdb, hd'⟩
  -- show c is a greatest common divisor of b and r
  have c_divide_b : c ∣ b := ⟨t, ht⟩
  have c_divide_r : c ∣ r := by
    have := congrArg (. - q*b) hab
    simp at this
    conv at this => rhs; rw [← subtract_definition, add_right_commutative, add_inverse, zero_add]
    rw [hs, ht, ← subtract_definition, negate_multiply_equal_negate_multiply, multiply_left_commutative, ← left_distributive] at this
    exact Exists.intro (s + -q * t) this.symm
  have := gcd_unique_up_to_sign (Meet.mk hda hdb hd') (Meet.mk c_divide_b c_divide_r sorry)
  simp [magnitude_equal_of_nonnegative, hc, hd] at this
  exact this.symm

def gcd (a b : ℤ) : Σ' d : ℤ, PProd (0 ≤ d) (GreatestCommonDivisor a b d) := sorry

def gcd' (a b : ℤ) : ℤ := (gcd a b).fst

-- TODO: Show that Divides is a preorder and DividesNonnegative is a partial order
-- TODO: Formulate Meet/Join Lattice and lemmas and then GreatestCommonDivisor doesn't need to exist, just say gcd(a, b) forms a meet lattice w.r.t `divides` on ℤ≥0

-- TODO: Define gcd (a b : ℤ) : Σ' d : ℤ, 0 ≤ d ∧ @Meet Divide a b d
-- TODO: Write gcd_unique
-- TODO: Write Bezout's lemma
-- TODO: Formujlate Coprime
-- TODO: Write Proposition 7.1.29
-- TODO: Write Proposition 7.1.32
-- TODO: Formulate Definition 7.1.38
-- TODO: Write Exercise 7.1.39
-- TODO: Formulate Definition 7.1.40
-- TODO: Write Exercise 7.1.41

-- TODO: Formulate Definition 7.2.1
-- TODO: Formulate Definition 7.2.6
-- TODO: Proposition 7.2.7
-- TODO: Proposition 7.2.9
-- TODO: Proposition 7.2.10
-- TODO: Proposition 7.2.11
-- TODO: Proposition 7.2.12
-- TODO: Definition 7.2.15

-- TODO: Theorem 7.2.22
