import Barb.Algebra
import Barb.Data.Natural
import Barb.Data.Option
import Barb.Function
import Barb.Logic
import Barb.Quotient
import Barb.Syntax

open Natural (zero successor)

def IntegerEquivalent : (ℕ × ℕ) → (ℕ × ℕ) → Prop
  | (n, m), (n', m') => n + m' = n' + m

theorem IntegerEquivalent.reflexive : Relation.Reflexive IntegerEquivalent :=
  λ _ => rfl
  
theorem IntegerEquivalent.symmetric : Relation.Symmetric IntegerEquivalent := Eq.symm

theorem IntegerEquivalent.transitive : Relation.Transitive IntegerEquivalent
  | (a, b), (c, d), (e, f), (h₁ : a + d = c + b), (h₂ : c + f = e + d) => by
    have := calc
      (c + d) + (a + f) = (a + d) + (c + f) := by simp [Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative]
      _ = (c + b) + (e + d) := by simp [h₁, h₂]
      _ = (c + d) + (e + b) := by simp [Natural.add_associative, Natural.add_commutative, Natural.add_left_commutative]
    show a + f = e + b
    exact Natural.add_left_cancel this

theorem IntegerEquivalent.is_equivalence : Equivalence IntegerEquivalent :=
  { refl := IntegerEquivalent.reflexive, symm := IntegerEquivalent.symmetric, trans := IntegerEquivalent.transitive }

instance instanceHasEquivIntegerEquivalent : HasEquiv (ℕ × ℕ) where
  Equiv := IntegerEquivalent
  
instance instanceSetoidIntegerEquivalent : Setoid (ℕ × ℕ) where
  r := IntegerEquivalent
  iseqv := IntegerEquivalent.is_equivalence

instance decideIntegerEquivalent (a b : ℕ × ℕ) : Decidable (a ≈ b) :=
  let (n, m) := a
  let (k, l) := b
  Natural.decideEqual (n + l) (k + m)

instance decideIntegerEquivalentQuotientEqual : DecidableEq (Quotient instanceSetoidIntegerEquivalent) := inferInstance

def Integer := Quotient instanceSetoidIntegerEquivalent

namespace Integer

notation "ℤ" => Integer

instance decideEqual : DecidableEq Integer := decideIntegerEquivalentQuotientEqual

instance : OfNat Integer n where
  ofNat := ⟦(Natural.natToNatural n, 0)⟧

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
    (u*w + v*x)*y + (u*x + v*w)*z 
      = ((u*w)*y + (v*x)*y) + (u*x + v*w)*z       := congrArg (. + _) (Natural.right_distributive _ _ _)
    _ = ((u*w)*y + (v*x)*y) + ((u*x)*z + (v*w)*z) := congrArg (_ + .) (Natural.right_distributive _ _ _)
    _ = (u*w)*y + ((v*x)*y + ((u*x)*z + (v*w)*z)) := Natural.add_associative _ _ _
    _ = (u*w)*y + (((v*x)*y + (u*x)*z) + (v*w)*z) := congrArg (_ + .) (Natural.add_associative _ _ _).symm
    _ = (u*w)*y + (((u*x)*z + (v*x)*y) + (v*w)*z) := congrArg (λ x => _ + (x + _)) (Natural.add_commutative _ _)
    _ = (u*w)*y + ((u*x)*z + ((v*x)*y + (v*w)*z)) := congrArg (_ + .) (Natural.add_associative _ _ _)
    _ = (u*w)*y + ((u*x)*z + ((v*w)*z + (v*x)*y)) := congrArg (λ x => _ + (_ + x)) (Natural.add_commutative _ _)
    _ = ((u*w)*y + (u*x)*z) + ((v*w)*z + (v*x)*y) := (Natural.add_associative _ _ _).symm
    _ = (u*(w*y) + (u*x)*z) + ((v*w)*z + (v*x)*y) := congrArg (λ x => (x + _) + _) (Natural.multiply_associative _ _ _)
    _ = (u*(w*y) + u*(x*z)) + ((v*w)*z + (v*x)*y) := congrArg (λ x => (_ + x) + _) (Natural.multiply_associative _ _ _)
    _ = u*(w*y + x*z) + ((v*w)*z + (v*x)*y)       := congrArg (. + _) (Natural.left_distributive _ _ _).symm
    _ = u*(w*y + x*z) + (v*(w*z) + (v*x)*y)       := congrArg (λ x => _ + (x + _)) (Natural.multiply_associative _ _ _)
    _ = u*(w*y + x*z) + (v*(w*z) + v*(x*y))       := congrArg (λ x => _ + (_ + x)) (Natural.multiply_associative _ _ _)
    _ = u*(w*y + x*z) + v*(w*z + x*y)             := congrArg (_ + .) (Natural.left_distributive _ _ _).symm
  have h1 : d = f := calc
    d = (n*k + m*l)*p + (n*l + m*k)*q := rfl
    _ = n*(k*p + l*q) + m*(k*q + l*p) := r
    _ = f := rfl
  have h2 : e = g := calc
    e = n*(k*q + l*p) + m*(k*p + l*q) := rfl
    _ = (n*k + m*l)*q + (n*l + m*k)*p := r.symm
    _ = g := rfl
  calc
    ((n*k + m*l)*p + (n*l + m*k)*q) + (n*(k*q + l*p) + m*(k*p + l*q)) 
      = d + (n*(k*q + l*p) + m*(k*p + l*q)) := congrArg (. + _) rfl 
    _ = d + e := congrArg (_ + .) rfl
    _ = f + e := congrArg (. + _) h1
    _ = f + g := congrArg (_ + .) h2
    _ = (n*(k*p + l*q) + m*(k*q + l*p)) + g := congrArg (. + _) rfl
    _ = (n*(k*p + l*q) + m*(k*q + l*p)) + ((n*k + m*l)*q + (n*l + m*k)*p) := rfl

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
  add_identity := add_zero
  add_inverse := add_inverse

  multiply_commutative := multiply_commutative
  multiply_associative := multiply_associative
  multiply_identity := multiply_one

  left_distributive := left_distributive
  right_distributive := right_distributive

theorem zero_add (a : ℤ) : 0 + a = a := by
  rw [add_commutative, add_zero]

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
    
@[simp]
def subtract (a b : ℤ) : ℤ := a + (-b)

instance : Sub Integer where sub := subtract

@[simp]
theorem subtract_definition (a b : ℤ) : a + (-b) = a - b := rfl

theorem negate_zero : (0 : ℤ) = (-0 : ℤ) := rfl

@[simp]
theorem negate_negate : Function.Involutive negate := by
  apply Quotient.ind
  intro (n, m)
  rfl

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
  calc
    -(a - b) = -(a + -b) := rfl
    _ = -a + (- -b) := negate_add a (-b)
    _ = -a + b := congrArg (_ + .) (negate_negate _)
    _ = b + -a := add_commutative _ _
    _ = b - a := subtract_definition _ _

theorem subtract_subtract_self (a b : ℤ) : a - (a - b) = b := by
  rw [← subtract_definition, negate_subtract, ← subtract_definition, 
    add_commutative (b) (-a), add_negate_cancel_left]
    
-- Looked at proof in lean std which uses negate_equal_of_add_equal_zero. This was foreign to me.
-- Observation is that conclusion is of the form we would like here, we need a' = a * b and b' = -a * b, and then the theorem will tell us -(a * b) = -a * b, which is our desired result. So we need to provide (-(a * b)) + (-a * b) = 0, which we can do.
theorem negate_multiply_equal_negate_multiply (a b : ℤ) : -(a * b) = -a * b := by
  apply Eq.symm
  apply negate_equal_of_add_equal_zero
  rw [← right_distributive, add_commutative, add_inverse, zero_multiply]

theorem negate_multiply_equal_multiply_negate (a b : ℤ) : -(a * b) = a * -b := by
  rw [multiply_commutative, negate_multiply_equal_negate_multiply, multiply_commutative]

theorem equal_zero_of_multiply_equal_zero : ∀ {a b : ℤ}, a * b = 0 → a = 0 ∨ b = 0 := by
  apply Quotient.ind₂
  intro (n, m) (k, l) h_quotient
  have h_equivalent : n*k + m*l = n*l + m*k := calc
    n*k + m*l = (n*k + m*l) + 0 := (Natural.add_zero _).symm
    _ = 0 + (n*l + m*k) := Quotient.exact h_quotient
    _ = n*l + m*k := Natural.zero_add _
  have f {w x y z : ℕ} (h_less : w < x) (h_equivalent : w*y + x*z = w*z + x*y) : (y, z) ≈ (0, 0) := by
  { let ⟨a, h_positive, (h_exists : w + a = x)⟩ := Natural.equal_add_positive_of_less_than h_less
    have h₁ := calc
      (w*y + w*z) + a*z = w*y + (w*z + a*z) := Natural.add_associative _ _ _
      _ = w*y + (w + a)*z := congrArg (_ + .) (Natural.right_distributive _ _ _).symm
      _ = w*y + x*z := congrArg (λ x => _ + (x * _)) h_exists
      _ = w*z + x*y := h_equivalent
      _ = w*z + (w + a)*y := congrArg (λ x => _ + (x * _)) h_exists.symm
      _ = w*z + (w*y + a*y) := congrArg (_ + .) (Natural.right_distributive _ _ _)
      _ = (w*z + w*y) + a*y := (Natural.add_associative _ _ _).symm
      _ = (w*y + w*z) + a*y := congrArg (. + _) (Natural.add_commutative _ _)
    have h₂ : a*z = a*y := Natural.add_left_cancel h₁
    have h₃ : z = y := Natural.multiply_left_cancel h₂ h_positive
    calc
      y + 0 = y := Natural.add_zero _
      _ = z := h₃.symm
      _ = 0 + z := (Natural.zero_add _).symm }
  cases less_than_trichotomous n m with
  | inl h_less =>
    apply Or.inr
    apply Quotient.sound
    exact f h_less h_equivalent
  | inr h_other => cases h_other with
    | inl h_equal => 
      apply Or.inl
      apply Quotient.sound
      calc
        n + 0 = n := Natural.add_zero n
        _ = m := h_equal
        _ = 0 + m := (Natural.zero_add m).symm
    | inr h_greater =>
      apply Or.inr
      apply Quotient.sound
      apply f h_greater 
      calc
        m*k + n*l = n*l + m*k := Natural.add_commutative _ _
        _ = n*k + m*l := h_equivalent.symm
        _ = m*l + n*k := Natural.add_commutative _ _

theorem multiply_equal_zero_of_equal_zero : ∀ {a b : ℤ}, a = 0 ∨ b = 0 → a * b = 0 := by
  apply Quotient.ind₂
  intro (n, m) (k, l) h_quotient
  suffices ∀ {w x y z : ℕ}, (h_zero : Quotient.mk' (w, x) = (0 : ℤ)) → multiply (Quotient.mk' (w, x)) (Quotient.mk' (y, z)) = 0 by
  { cases h_quotient with
    | inl h_nm => exact this h_nm
    | inr h_kl => exact (multiply_commutative _ _).trans (this h_kl) }
  intro w x y z h_zero
  apply Quotient.sound
  have h_equal := calc
    w = w + 0 := (Natural.add_zero _).symm
    _ = 0 + x := Quotient.exact h_zero
    _ = x := Natural.zero_add _
  have h_equivalent := calc
    w*y + x*z = x*z + w*y := Natural.add_commutative _ _
    _ = w*z + w*y := congrArg (λ x => (x * _) + _) h_equal.symm
    _ = w*z + x*y := congrArg (λ x => _ + (x * _)) h_equal
  calc
    (w*y + x*z) + 0 = w*y + x*z := Natural.add_zero _
    _ = w*z + x*y := h_equivalent
    _ = 0 + (w*z + x*y) := (Natural.zero_add _).symm

theorem multiply_left_commutative (n m k : ℤ) : n * (m * k) = m * (n * k) := by
  rw [← multiply_associative, multiply_commutative n m, multiply_associative]

theorem multiply_right_commutative (n m k : ℤ) : (n * m) * k = (n * k) * m := by
  rw [multiply_associative, multiply_commutative m k, ← multiply_associative]

-- Looked at hints, attempted a lifting proof and that's probably way overkill
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
  
theorem multiply_not_equal_zero_of_not_equal_zero {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  apply hb
  apply Integer.multiply_left_cancel (a := a)
  calc
    a * b = 0 := h
    _ = a * 0 := (Integer.multiply_zero _).symm
  exact ha

theorem not_equal_zero_of_multiply_not_equal_zero {a b : ℤ} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  not_or.mp (mt multiply_equal_zero_of_equal_zero h)

def ofNatural (n : ℕ) : ℤ := Quotient.mk instanceSetoidIntegerEquivalent (n, 0)

instance : Coe Natural Integer := ⟨ofNatural⟩

theorem ofNatural_add (n m : ℕ) : ofNatural (n + m) = ofNatural n + ofNatural m := rfl

theorem ofNatural_multiply (n m : ℕ) : ofNatural (n * m) = ofNatural n * ofNatural m := by
  unfold ofNatural
  apply Quotient.sound
  show (n * m) + (n * 0 + 0 * m) = (n * m + 0 * 0) + 0
  simp [Natural.add_zero, Natural.zero_add, Natural.multiply_zero, Natural.zero_multiply]

theorem ofNatural_injective : Function.Injective ofNatural := by
  intro a b h
  rw [← Natural.add_zero a, Quotient.exact h, Natural.add_zero]
  
theorem ofNatural_zero : ofNatural 0 = (0 : ℤ) := rfl

def LessEqual (a b : ℤ) : Prop := ∃ (n : ℕ), a + ↑n = b

instance : LE Integer where
  le := LessEqual
  
@[simp] theorem less_equal_definition : (a ≤ b) = (LessEqual a b) := rfl 

theorem LessEqual.reflexive : Relation.Reflexive LessEqual :=
  λ _ => Exists.intro 0 (add_zero _)

theorem LessEqual.antisymmetric : Relation.AntiSymmetric LessEqual := by
  intro a b ⟨n, hn⟩ ⟨m, hm⟩
  suffices m = 0 ∧ n = 0 
  by rw [← add_zero a, ← ofNatural_zero, ← this.right, hn]
  apply Natural.equal_zero_of_add_equal_zero
  apply ofNatural_injective
  apply add_left_cancel (a := b)
  rw [ofNatural_add, ← add_associative, hm, hn, ofNatural_zero, add_zero]

theorem LessEqual.transitive : Relation.Transitive LessEqual := by
  intro a b c ⟨n, (ha : a + ↑n = b)⟩ ⟨m, (hb : b + ↑m = c)⟩
  apply Exists.intro ↑(n + m)
  rw [ofNatural_add, ← add_associative, ha, hb]
  
theorem less_equal_of_subtract_nonnegative {a b : ℤ} : b - a ≥ 0 → a ≤ b := by
  intro ⟨n, (h : 0 + ↑n = b - a)⟩
  apply Exists.intro n
  rw [add_commutative a ↑n, ← zero_add (↑n + a), ← add_associative, h, 
    ← subtract_definition, add_associative, add_inverse_left, add_zero]

theorem subtract_nonnegative_of_less_equal {a b : ℤ} : a ≤ b → b - a ≥ 0 := by
  intro ⟨n, (h : a + ↑n = b)⟩
  apply Exists.intro n
  rw [← add_inverse a, add_right_commutative, h, subtract_definition]

theorem nonnegative_of_positive_greater_equal_negative {n m : ℕ} : n ≥ m → (0 : ℤ) ≤ ⟦(n, m)⟧ := by
  intro ⟨a, (ha : m + a = n)⟩
  apply Exists.intro a
  apply Quotient.sound
  show (0 + a) + m = n + 0
  simp [Natural.add_zero, Natural.add_commutative, ha]

theorem positive_greater_equal_negative_of_nonnegative {n m : ℕ} : (0 : ℤ) ≤ ⟦(n, m)⟧ → n ≥ m := by
  intro ⟨a, (ha : (0 : ℤ) + ↑a = ⟦(n, m)⟧)⟩
  have : (0 + a) + m = n + (0 + 0) := Quotient.exact ha
  simp [Natural.zero_add, Natural.add_commutative] at this
  exact (Exists.intro a this)
    
instance decideNonNegative (a : ℤ) : Decidable (0 ≤ a) :=
  Quotient.recOnSubsingleton a 
  λ ((n, m) : ℕ × ℕ) =>
  if h : n ≥ m then
    isTrue (nonnegative_of_positive_greater_equal_negative h)
  else
    isFalse (mt positive_greater_equal_negative_of_nonnegative h)
    
instance decideLessEqual (a b : ℤ) : Decidable (a ≤ b) :=
  if h : 0 ≤ b - a then
    isTrue (less_equal_of_subtract_nonnegative h)
  else
    isFalse (mt subtract_nonnegative_of_less_equal h)

theorem LessEqual.strongly_connected : Relation.StronglyConnected LessEqual :=
  have lift_less_equal {n m k l : ℕ} : n + l ≤ k + m → LessEqual ⟦(n, m)⟧ ⟦(k, l)⟧ := by
  { intro ⟨a, (ha : (n + l) + a = k + m)⟩
    apply Exists.intro a
    apply Quotient.sound
    simp
    show (n + a) + l = k + m
    rw [Natural.add_right_commutative, ha]
  }
  Quotient.ind₂ λ (p, q) (s, t) =>
  Or.implies lift_less_equal lift_less_equal (Natural.LessEqual.strongly_connected (p + t) (s + q))
  
instance instanceTotalOrder : TotalOrder Integer where
  less_equal_reflexive := LessEqual.reflexive
  less_equal_antisymmetric := LessEqual.antisymmetric
  less_equal_transitive := LessEqual.transitive
  less_equal_strongly_connected := LessEqual.strongly_connected
  decidableEqual := decideEqual
  decidableLessEqual := decideLessEqual

theorem add_left_less_equal {b c : ℤ} (h : b ≤ c) (a : ℤ) : a + b ≤ a + c := by
  let ⟨n, hn⟩ := h
  apply Exists.intro n
  rw [add_associative, hn]

theorem add_right_less_equal {a b : ℤ} (h : a ≤ b) (c : ℤ) : a + c ≤ b + c := by
  rw [add_commutative a c, add_commutative b c]
  exact add_left_less_equal h c

theorem less_equal_of_add_less_equal_left {a b c : ℤ} (h : a + b ≤ a + c) : b ≤ c := by
  have := add_left_less_equal h (-a)
  simp [negate_add_cancel_left] at this
  exact this
  
theorem less_equal_of_add_less_equal_right {a b c : ℤ} (h : a + c ≤ b + c) : a ≤ b := by
  rw [add_commutative a c, add_commutative b c] at h
  exact less_equal_of_add_less_equal_left h

theorem add_less_equal_add {a b c d : ℤ} (hac : a ≤ c) (hbd : b ≤ d) : a + b ≤ c + d :=
  less_equal_transitive (add_right_less_equal hac b) (add_left_less_equal hbd c)
  
theorem less_equal_add_of_nonnegative_left {a b : ℤ} (h : b ≥ 0) : a ≤ b + a := by
  have := add_less_equal_add h (less_equal_reflexive a)
  rw [zero_add] at this
  exact this
  
theorem less_equal_add_of_nonnegative_right {a b : ℤ} (h : b ≥ 0) : a ≤ a + b := by
  rw [add_commutative a b]
  exact less_equal_add_of_nonnegative_left h
  
theorem negate_less_equal (a b : ℤ) (h : a ≤ b) : -b ≤ -a := by
  have ha := add_right_less_equal h (-a)
  rw [add_inverse, add_commutative] at ha
  have hb := add_right_less_equal ha (-b)
  rw [zero_add, add_associative (-a) b (-b), add_inverse, add_zero] at hb
  exact hb

theorem multiply_less_equal_of_nonnegative_left {a b c : ℤ} (h_less_equal : b ≤ c) (h_positive : a ≥ 0) : a * b ≤ a * c := by
  let ⟨n, hn⟩ := h_less_equal
  let ⟨m, hm⟩ := h_positive
  rw [zero_add] at hm
  apply Exists.intro ↑(m * n)
  rw [ofNatural_multiply, hm, ← left_distributive, hn]

theorem multiply_less_equal_of_nonnegative_right {a b c : ℤ} (h_less_equal : a ≤ b) (h_positive : c ≥ 0) : a * c ≤ b * c := by
  rw [multiply_commutative a c, multiply_commutative b c]
  exact multiply_less_equal_of_nonnegative_left h_less_equal h_positive
  
def LessThan := instanceTotalOrder.less_than

theorem less_than_of_subtract_positive {a b : ℤ} : 0 < b - a → a < b := by
  intro h
  have ⟨hp, hn⟩ := less_than_equivalent_less_equal_not_less_equal.mp h
  apply less_than_equivalent_less_equal_not_less_equal.mpr
  apply And.intro
  . exact less_equal_of_subtract_nonnegative hp
  . intro h'
    have := add_right_less_equal h' (-a)
    simp [subtract_self] at this
    exact hn this

theorem subtract_positive_of_less_than {a b : ℤ} : a < b → 0 < b - a := by
  intro h
  have ⟨hp, hn⟩ := less_equal_not_less_equal_of_less_than h
  apply less_than_of_less_equal_not_less_equal
  . exact subtract_nonnegative_of_less_equal hp
  . intro h'
    have := calc
      b = b + 0 := (add_zero _).symm
      _ = b + (a - a) := congrArg (_ + .) (subtract_self a).symm
      _ = b + (-a + a) := congrArg (_ + .) (add_commutative _ _)
      _ = (b + -a) + a := (add_associative _ _ _).symm
      _ ≤ 0 + a := add_right_less_equal h' a
      _ = a := zero_add _
    exact absurd this hn

theorem add_left_less_than {b c : ℤ} (h : b < c) (a : ℤ) : a + b < a + c := by
  let ⟨h_less_equal, h_not_greater_equal⟩ := h
  apply less_than_of_less_equal_not_less_equal
  . exact add_left_less_equal h_less_equal a
  . intro h_greater_equal
    have : c ≤ b := (less_equal_of_add_less_equal_left h_greater_equal)
    exact absurd this h_not_greater_equal

theorem add_right_less_than {a b : ℤ} (h : a < b) (c : ℤ) : a + c < b + c := by
  rw [add_commutative a c, add_commutative b c]
  exact add_left_less_than h c

theorem negate_less_than (a b : ℤ) (h : a < b) : -b < -a := by
  have ha := add_left_less_than h (-b)
  rw [add_inverse_left] at ha
  have hb := add_right_less_than ha (-a)
  rw [zero_add, add_associative, add_inverse, add_zero] at hb
  exact hb

/-
theorem less_equal_multiply_cancel_of_positive {a b c : ℤ} (h_less_equal : a * b ≤ a * c) (h_not_zero : a > 0) : b ≤ c := by
  let ⟨n, hn⟩ := subtract_nonnegative_of_less_equal h_less_equal
  rw [zero_add, ← subtract_definition, negate_multiply_equal_multiply_negate, ← left_distributive, ] at hn
  

theorem multiply_less_than_of_positive_left (a b c : ℤ) : b < c → a > 0 → a * b < a * c := by
  intro h_less_than h_positive
  have ⟨h_less_equal, h_not_less_equal⟩ := less_equal_not_less_equal_of_less_than h_less_than
  have ⟨h_nonnegative, h_not_negative⟩ := less_equal_not_less_equal_of_less_than h_positive
  apply less_than_of_less_equal_not_less_equal
  . exact multiply_less_equal_of_nonnegative_left h_less_equal h_nonnegative
  . sorry

theorem multiply_less_than_of_positive_right (a b c : ℤ) : a < b → c > 0 → a * c < b * c := sorry
-/

theorem ofNatural_nonnegative (n : ℕ) : ↑n ≥ (0 : ℤ) :=
  Exists.intro n (zero_add n)
  
theorem equal_ofNatural_of_nonnegative : ∀ {a : ℤ}, a ≥ 0 → ∃ n : ℕ, ↑n = a := by
  apply Quotient.ind
  intro (n, m) ⟨a, ha⟩
  simp [zero_add] at ha
  exact Exists.intro a ha

abbrev NonNegativeInteger := {a : ℤ // a ≥ 0}
abbrev PositiveInteger := {a : ℤ // a > 0}
abbrev NonZeroInteger := {a : ℤ // a ≠ 0}
abbrev NegativeInteger := {a : ℤ // a < 0}
abbrev NonPositiveInteger := {a : ℤ // a ≤ 0}

-- TODO: Remove Natural substraction entirely in favor of the distance metric
namespace NonNegativeInteger

def predecessor : ℕ → ℕ
  | 0 => 0
  | successor n => n

def subtractTruncated : ℕ → ℕ → ℕ
  | n, 0 => n
  | n, successor m => predecessor (subtractTruncated n m)

instance : Sub Natural where
  sub := subtractTruncated

@[simp] theorem subtract_zero (n : ℕ) : n - 0 = n := rfl

@[simp] theorem successor_subtract_successor_equal_subtract (n m : ℕ) : successor n - successor m = n - m := by
  induction m with
  | zero      => exact rfl
  | successor m ih => exact congrArg predecessor ih

theorem subtract_successor (n m : ℕ) : n - successor m = predecessor (n - m) := rfl

theorem successor_subtract_successor (n m : ℕ) : successor n - successor m = n - m :=
  successor_subtract_successor_equal_subtract n m

theorem add_subtract_self_left (n m : ℕ) : (n + m) - n = m := by
  induction n with
  | zero => rfl
  | successor n ih =>
    rw [Natural.successor_add, successor_subtract_successor]
    exact ih

theorem add_subtract_self_right (n m : ℕ) : (n + m) - m = n := by
  rw [Natural.add_commutative, add_subtract_self_left]

@[simp]
theorem predecessor_zero : predecessor 0 = 0 := rfl

@[simp]
theorem predecessor_successor (n : ℕ) : predecessor (successor n) = n := rfl

theorem successor_predecessor {n : ℕ} (h : n ≠ 0) : successor (predecessor n) = n := by
  induction n with
  | zero => contradiction
  | successor ih => rfl

theorem successor_predecessor_equal_of_positive : ∀ {n : ℕ}, 0 < n → successor (predecessor n) = n
  | successor _, _ => rfl

theorem predecessor_less_equal : ∀ (n : ℕ), predecessor n ≤ n
  | zero => Natural.zero_less_equal _
  | successor n => by
    simp
    exact less_equal_of_less_than (Natural.less_than_successor n)

theorem predecessor_less_than : ∀ {n : ℕ}, n ≠ 0 → predecessor n < n
  | zero,   h => absurd rfl h
  | successor n, _ => Natural.less_than_successor_of_less_equal (less_equal_reflexive n)

theorem subtract_less_equal (n m : ℕ) : n - m ≤ n := by
  induction m with
  | zero      => exact less_equal_reflexive (n - 0)
  | successor m ih => exact less_equal_transitive (predecessor_less_equal (n - m)) ih

theorem subtract_less_than : ∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
  | 0, _, h1, _ => absurd h1 (less_than_irreflexive 0)
  | successor _, 0, _, h2 => absurd h2 (less_than_irreflexive 0)
  | successor n, successor m, _, _ =>
    Eq.symm (successor_subtract_successor_equal_subtract n m) ▸
      show n - m < successor n from
      Natural.less_than_successor_of_less_equal (subtract_less_equal n m)

theorem subtract_less_equal_successor_subtract (n m : ℕ) : n - m ≤ n.successor - m := by
  cases m with
  | zero => apply less_equal_of_less_than; apply Natural.less_than_successor
  | successor m => rw [subtract_successor, successor_subtract_successor]; apply predecessor_less_equal

theorem zero_less_than_subtract_of_less_than (n m : ℕ) (h : m < n) : 0 < n - m := by
  induction n with
  | zero => exact absurd h (Natural.not_less_than_zero m)
  | successor n ih =>
    have foo := Natural.successor_less_equal_of_less_than h
    match Decidable.equal_or_less_than_of_less_equal foo with
    | Or.inl h => injection h with h; subst h; rw [← Natural.add_one, add_subtract_self_left]; decide
    | Or.inr h =>
      have : 0 < n - m := ih (Natural.less_than_of_successor_less_than_successor h)
      exact less_than_of_less_than_of_less_equal this (subtract_less_equal_successor_subtract _ _)

theorem subtract_successor_less_than_self (n m : ℕ) (h : m < n) : n - successor m < n - m := by
  rw [subtract_successor]
  apply predecessor_less_than
  apply Natural.not_equal_zero_of_less_than
  apply zero_less_than_subtract_of_less_than
  exact h

theorem subtract_not_equal_zero_of_less_than : {n m : ℕ} → n < m → m - n ≠ 0
  | 0, 0, h => absurd h (less_than_irreflexive 0)
  | 0, successor m, _ => Natural.successor_not_equal_zero m
  | successor n, 0, h => absurd h (Natural.not_less_than_zero n.successor)
  | successor n, successor m, h => by 
    rw [successor_subtract_successor]
    exact subtract_not_equal_zero_of_less_than (Natural.less_than_of_successor_less_than_successor h)

theorem add_subtract_of_less_equal {n m : ℕ} (h : n ≤ m) : n + (m - n) = m := by
  induction n with
  | zero => 
    -- TODO: Weird zero definitally not equal to 0 stuff
    calc
      zero + (m - zero) = (m - zero) := Natural.zero_add _
      _  = m := subtract_zero m
  | successor n ih =>
    have hne : m - n ≠ 0 := subtract_not_equal_zero_of_less_than (Natural.less_than_of_successor_less_equal h)
    have : n ≤ m := Natural.less_equal_of_successor_less_equal h
    rw [subtract_successor, Natural.successor_add, ← Natural.add_successor, successor_predecessor hne, ih this]

@[simp] theorem subtract_add_cancel {n m : ℕ} (h : m ≤ n) : (n - m) + m = n := by
  rw [Natural.add_commutative, add_subtract_of_less_equal h]

/-
Worth talking about how we figured this all out and how it might be further 
cleaned up. It's all a bit silly if you consider what this would all look like 
without proof-irrelevance.

https://github.com/Julian-Kuelshammer/summer_maths_it_camp/blob/main/src/easy_mode/sheet10.lean
-/

def preToNatural' : ℕ × ℕ → Option ℕ
  | (n, m) => if n ≥ m then some (n - m) else none

@[simp]
theorem preToNatural_none (x : ℕ × ℕ) (h : x.1 < x.2) : preToNatural' x = none := by
  have := not_less_equal_of_greater_than h
  simp [preToNatural', not_less_equal_of_greater_than h]
  
@[simp]
theorem preToNatural_some (x : ℕ × ℕ) (h : x.1 ≥ x.2) : preToNatural' x = some (x.1 - x.2) := by 
  simp [preToNatural', h]
  
def toNatural' : ℤ → Option ℕ :=
  Quotient.lift preToNatural' <| by
  intro (n, m) (k, l) (h : n + l = k + m)
  cases Decidable.em (n ≥ m) 
  <;> cases Decidable.em (k ≥ l)
  <;> simp_all [preToNatural', preToNatural_none, preToNatural_some]
  case inl.inl hnm hkl =>
    apply Natural.add_right_cancel (k := m + l)
    rw [← Natural.add_associative, subtract_add_cancel, h, ← subtract_add_cancel hkl, 
      Natural.add_associative (k - l) l m, Natural.add_commutative l m, subtract_add_cancel]
    exact hkl
    exact hnm
  case inl.inr hnm hkl =>
    rw [Natural.add_commutative k m] at h
    have := Natural.right_greater_equal_of_add_left_less_equal h.symm hnm
    exact absurd this hkl
  case inr.inl hnm hkl =>
    rw [Natural.add_commutative n l] at h
    have := Natural.right_greater_equal_of_add_left_less_equal h hkl
    exact absurd this hnm

def toNatural : NonNegativeInteger → ℕ
  | (⟨a, a_nonnegative⟩) => 
    Option.get (toNatural' a) <| by
    have ⟨n, hn⟩ := a_nonnegative
    rw [zero_add, ofNatural] at hn
    rw [toNatural', ← hn, Quotient.lift_construct, preToNatural']
    simp [Natural.zero_less_equal, subtract_zero, ite_true, Option.isSome]
    
def fromNatural (n : ℕ) : NonNegativeInteger :=
  ⟨n, ofNatural_nonnegative n⟩

theorem fromNatural_toNatural_left_inverse : Function.LeftInverse toNatural fromNatural := by
  intro n
  simp [fromNatural, ofNatural, toNatural, toNatural']

theorem toNatural_fromNatural_left_inverse : Function.LeftInverse fromNatural toNatural := by
  intro ⟨a, b, h⟩
  rw [zero_add, ofNatural] at h
  subst h
  simp [toNatural, toNatural', fromNatural, ofNatural]
  
end NonNegativeInteger
