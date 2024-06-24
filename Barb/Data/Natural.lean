import Barb.Function
import Barb.Logic
import Barb.Order

inductive Natural where
  | zero : Natural
  | successor : Natural → Natural

namespace Natural

open Natural (zero successor)

def fromNat : Nat → Natural
  | Nat.zero => Natural.zero
  | Nat.succ n => Natural.successor (fromNat n)

def toNat : Natural → Nat
  | Natural.zero => Nat.zero
  | Natural.successor n => Nat.succ (toNat n)

instance : OfNat Natural n where
  ofNat := fromNat n

instance : ToString Natural where
  toString := toString ∘ toNat

notation "ℕ" => Natural

theorem zero_definition : zero = 0 := rfl

theorem successor_not_equal_zero (n : ℕ) : successor n ≠ 0 :=
  Natural.noConfusion

theorem successor_injective : Function.Injective successor :=
  λ h => (Natural.noConfusion h) id

theorem successor_not_equal_self (n : ℕ) : successor n ≠ n := by
  induction n with
  | zero => exact successor_not_equal_zero 0
  | successor n ih => intro h; exact ih (successor_injective h)

def add : ℕ → ℕ → ℕ
  | zero, m => m
  | successor n, m => successor (add n m)

instance : Add Natural where
  add := add

@[simp] theorem add_definition : add n m = n + m := rfl

theorem zero_add (n : ℕ) : 0 + n = n := rfl

theorem successor_add (n m : ℕ) : (successor n) + m = successor (n + m) := rfl

@[simp] theorem add_zero (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => exact zero_add 0
  | successor n ih => calc
    (successor n) + 0 = successor (n + 0) := successor_add n 0
    _                 = successor n       := congrArg successor ih

theorem add_successor (n m : ℕ) : n + (successor m) = successor (n + m) := by
  induction n with
  | zero => calc
    0 + (successor m) = successor m       := zero_add (successor m)
    _                 = successor (0 + m) := congrArg successor (zero_add m)
  | successor n ih => calc
    (successor n) + (successor m) = successor (n + (successor m)) := successor_add n (successor m)
    _                             = successor (successor (n + m)) := congrArg successor ih

theorem add_commutative (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero => calc
    0 + m = m     := zero_add m
    _     = m + 0 := (add_zero m).symm
  | successor n ih => calc
    (successor n) + m = successor (n + m) := successor_add n m
    _                 = successor (m + n) := congrArg successor ih
    _                 = m + (successor n) := (add_successor m n).symm

theorem add_associative (n m k : ℕ) : (n + m) + k = n + (m + k) := by
  induction n with
  | zero => calc
    (0 + m) + k = m + k       := congrArg (. + k) (zero_add m)
    _           = 0 + (m + k) := zero_add (m + k)
  | successor n ih => calc
    ((successor n) + m) + k = (successor (n + m)) + k := congrArg (. + k) (successor_add n m)
    _                       = successor ((n + m) + k) := successor_add (n + m) k
    _                       = successor (n + (m + k)) := congrArg successor ih

theorem add_left_commutative (n m k : ℕ) : n + (m + k) = m + (n + k) := by
  rw [← add_associative, add_commutative n m, add_associative]
  
theorem add_right_commutative (n m k : ℕ) : (n + m) + k = (n + k) + m := by
  rw [add_associative, add_commutative m k, ← add_associative]

theorem add_left_cancel {n m k : ℕ} : n + m = n + k → m = k := by
  induction n with
  | zero => 
    intro h
    calc
      m = 0 + m := zero_add m
      _ = 0 + k := h
      _ = k     := zero_add k
  | successor n ih =>
    intro h
    have := calc
      successor (n + m) = (successor n) + m := (successor_add n m).symm
      _                 = (successor n) + k := h
      _                 = successor (n + k) := successor_add n k
    exact ih (successor_injective this)

theorem add_right_cancel {n m k : ℕ} (h : n + k = m + k) : n = m := by
  rw [add_commutative n k, add_commutative m k] at h
  exact add_left_cancel h

@[simp]
def distance : ℕ → ℕ → ℕ
  | zero, zero => 0
  | successor n, zero => successor n
  | zero, successor m => successor m
  | successor n, successor m => distance n m

theorem equal_of_distance_equal_zero : ∀ {n m : ℕ}, distance n m = 0 → n = m
  | zero, zero, _ => rfl
  | successor n, successor m, h => by
    unfold distance at h
    exact congrArg successor (equal_of_distance_equal_zero h)

theorem distance_equal_zero_of_equal : ∀ {n m : ℕ}, n = m → distance n m = 0
  | zero, zero, _ => rfl
  | successor n, successor m, h => by
    unfold distance
    exact distance_equal_zero_of_equal (successor_injective h)

theorem distance_self : ∀ (n : ℕ), distance n n = 0 :=
  λ _ => distance_equal_zero_of_equal rfl

theorem distance_zero_left : ∀ (n : ℕ), distance n 0 = n
  | zero => rfl
  | successor n => by unfold distance; rfl

theorem distance_commutative : ∀ (n m : ℕ), distance n m = distance m n
  | zero, zero => distance_zero_left _
  | zero, successor _ => distance_zero_left (successor _)
  | successor _, zero => distance_zero_left (successor _)
  | successor _, successor _ => by
    simp
    apply distance_commutative

theorem distance_zero_right (n : ℕ) : distance 0 n = n := by
  rw [distance_commutative, distance_zero_left]

theorem distance_add_add_right (n m k : ℕ) : distance (n + k) (m + k) = distance n m := by
  induction k with
  | zero =>
    have this : zero = 0 := rfl
    simp [this, add_zero]
  | successor k ih =>
    simp [add_successor]
    exact ih

theorem distance_add_add_left (n m k : ℕ) : distance (n + m) (n + k) = distance m k := by
  rw [add_commutative n m, add_commutative n k, distance_add_add_right]

theorem distance_equal_of_add_equal {n m k l : ℕ} (h : n + m = k + l) : distance n k = distance l m := by
  calc
    distance n k = distance (n + m) (k + m) := (distance_add_add_right n k m).symm
    _ = distance (k + l) (k + m) := congrArg (λ x => distance x _) h
    _ = distance l m := distance_add_add_left k l m

instance decideEqual : DecidableEq Natural
  | n, m => match h : distance n m with
    | zero => isTrue (equal_of_distance_equal_zero h)
    | successor a => isFalse (mt distance_equal_zero_of_equal (h ▸ successor_not_equal_zero a))

theorem add_positive {n m : ℕ} : n ≠ 0 → (n + m) ≠ 0 :=
  match n with
  | zero => absurd rfl
  | successor n => λ _ => successor_not_equal_zero (n + m)

theorem equal_zero_of_add_equal_zero {n m : ℕ} (h : n + m = 0) : n = 0 ∧ m = 0 := by
  apply And.intro
  . exact Decidable.of_not_not (mt add_positive (not_not_intro h))
  . have : m + n = 0 := (add_commutative n m).symm.trans h
    exact Decidable.of_not_not (mt add_positive (not_not_intro this))

theorem unique_predecessor_of_positive {n : ℕ} : n ≠ 0 → ∃! (m : ℕ), successor m = n :=
  match n with
  | zero => absurd rfl
  | successor n => λ _ => ExistsUnique.introduction n rfl (λ _ => successor_injective)

def LessEqual (n m : ℕ) : Prop := ∃ (a : ℕ), n + a = m

instance : LE Natural where
  le := LessEqual

@[simp] theorem less_equal_definition : (LessEqual n m) = (n ≤ m) := rfl

@[simp] theorem LessEqual.reflexive : Relation.Reflexive LessEqual :=
  λ n => Exists.intro 0 (add_zero n)

theorem LessEqual.antisymmetric : Relation.AntiSymmetric LessEqual := by
  intro n m ⟨a, (ha : n + a = m)⟩ ⟨b, (hb : m + b = n)⟩
  suffices a + b = 0 by 
  { have ⟨a_zero, _⟩ := equal_zero_of_add_equal_zero this
    rw [← add_zero n, ← a_zero, ha] }
  apply add_left_cancel (n := n)
  rw [← add_associative, ha, hb, add_zero]

theorem LessEqual.transitive : Relation.Transitive LessEqual := by
  intro n m k ⟨a, (ha : n + a = m)⟩ ⟨b, (hb : m + b = k)⟩
  apply Exists.intro (a + b)
  rw [← add_associative, ha, hb]

@[simp] theorem zero_less_equal (n : ℕ) : 0 ≤ n := 
  Exists.intro n (zero_add n)
  
theorem equal_zero_of_less_equal_zero : ∀ {n : ℕ}, n ≤ 0 → n = 0 := by
  intro n ⟨a, (h: n + a = 0)⟩
  have := equal_zero_of_add_equal_zero h
  exact this.left
  
theorem less_equal_of_successor_less_equal_successor {n m : ℕ} : successor n ≤ successor m → n ≤ m := by
  intro ⟨a, (h : successor n + a = successor m)⟩
  apply Exists.intro a
  apply successor_injective
  rw [← successor_add, h]
  
theorem successor_less_equal_successor_of_less_equal {n m : ℕ} : n ≤ m → successor n ≤ successor m := by
  intro ⟨a, (h : n + a = m)⟩
  have := calc
    successor n + a = successor (n + a) := successor_add _ _
    _ = successor m := congrArg successor h
  exact Exists.intro a this
  
theorem less_equal_successor_of_less_equal {n m : ℕ} : n ≤ m → n ≤ successor m := by
  intro ⟨a, (h : n + a = m)⟩
  have := calc
    n + successor a = successor (n + a) := add_successor _ _
    _ = successor m := congrArg successor h
  exact Exists.intro (successor a) this

def booleanLessEqual : ℕ → ℕ → Bool
  | zero, zero => true
  | zero, successor _ => true
  | successor _, zero => false
  | successor n, successor m => booleanLessEqual n m

theorem less_equal_of_boolean_less_equal_true {n m : ℕ} (h : (booleanLessEqual n m) = true) : n ≤ m :=
  match n, m with
  | zero, _ => zero_less_equal _
  | successor _, successor _ => successor_less_equal_successor_of_less_equal (less_equal_of_boolean_less_equal_true h)
  
theorem boolean_less_equal_true_of_less_equal : ∀ {n m : ℕ}, n ≤ m → (booleanLessEqual n m) = true
  | zero, m, _ => by cases m <;> rfl
  | successor n, successor m, h => by
    rw [booleanLessEqual]
    have := less_equal_of_successor_less_equal_successor h
    exact boolean_less_equal_true_of_less_equal this

instance decideLessEqual (n m : ℕ) : Decidable (n ≤ m) :=
  if h : (booleanLessEqual n m) = true then
    isTrue (less_equal_of_boolean_less_equal_true h)
  else
    isFalse (mt boolean_less_equal_true_of_less_equal h)

theorem LessEqual.strongly_connected : Relation.StronglyConnected LessEqual
  | zero, _ => Or.inl (zero_less_equal _)
  | successor _, zero => Or.inr (zero_less_equal _)
  | successor n, successor m =>
    Or.implies 
      successor_less_equal_successor_of_less_equal 
      successor_less_equal_successor_of_less_equal 
      (LessEqual.strongly_connected n m)

instance totalOrder : DecidableTotalOrder Natural where
  less_equal_reflexive := LessEqual.reflexive
  less_equal_antisymmetric := LessEqual.antisymmetric
  less_equal_transitive := LessEqual.transitive
  less_equal_strongly_connected := LessEqual.strongly_connected
  decideEqual := decideEqual
  decideLessEqual := decideLessEqual

def LessThan : ℕ → ℕ → Prop := strictPartialOrderOfPreorder.lt

theorem less_than_successor (n : ℕ) : n < successor n :=
  have := less_than_or_equal_of_less_equal (less_equal_successor_of_less_equal (less_equal_reflexive n))
  Or.resolve_right this (successor_not_equal_self n).symm

theorem less_than_of_successor_less_equal {n m : ℕ} (h : successor n ≤ m) : n < m :=
  less_than_of_less_than_of_less_equal (less_than_successor n) h

theorem less_than_successor_of_less_equal {n m : ℕ} (h : n ≤ m) : n < successor m := 
  less_than_of_less_equal_of_less_than h (less_than_successor m)

theorem successor_less_equal_of_less_than {n m : ℕ} (h : n < m) : successor n ≤ m :=
  have ⟨a, (ha : n + a = m)⟩ := less_equal_of_less_than h
  have hnm := not_equal_of_less_than h
  match a with
  | zero => absurd ((add_zero _).symm.trans ha) hnm
  | successor a => 
    have := calc
      successor n + a = successor (n + a) := successor_add _ _
      _ = n + successor a := (add_successor _ _).symm
      _ = m := ha
    Exists.intro a this

theorem less_equal_of_successor_less_equal {n m : ℕ} : successor n ≤ m → n ≤ m := 
  less_equal_of_less_than ∘ less_than_of_successor_less_equal
    
theorem less_than_of_successor_less_than_successor {n m : ℕ} : successor n < successor m → n < m :=
  less_than_of_successor_less_equal ∘ less_equal_of_successor_less_equal_successor ∘ successor_less_equal_of_less_than

theorem equal_zero_or_positive (n : ℕ) : n = 0 ∨ n > 0 :=
  Or.implies_left 
  Eq.symm
  (Or.commutative.mp (less_than_or_equal_of_less_equal (zero_less_equal n)))

theorem not_successor_less_equal_zero (n : ℕ) : ¬(successor n ≤ 0) := by
  intro ⟨a, (ha : successor n + a = 0)⟩
  rw [successor_add] at ha
  exact (successor_not_equal_zero _) ha

theorem zero_less_than_successor (n : ℕ) : successor n > 0 :=
  Or.resolve_left (equal_zero_or_positive (successor n)) (successor_not_equal_zero _)

theorem not_less_than_zero (n : ℕ) : ¬(n < 0) :=
  λ h => not_successor_less_equal_zero n (successor_less_equal_of_less_than h)

theorem zero_less_than_positive {n : ℕ} : n ≠ 0 → 0 < n :=
  Or.resolve_left (equal_zero_or_positive n)
  
theorem nonzero_of_less_than {n m : ℕ} (h : n < m) : m ≠ 0 :=
  match m with
  | zero => absurd h (not_less_than_zero _)
  | successor _ => successor_not_equal_zero _

theorem add_left_less_equal {m k : ℕ} (h : m ≤ k) (n : ℕ) : n + m ≤ n + k :=
  let ⟨a, (h₁ : m + a = k)⟩ := h
  have := calc
    n + m + a = n + (m + a) := add_associative n m a
    _         = n + k       := congrArg (n + .) h₁
  Exists.intro a this

theorem add_right_less_equal {n m : ℕ} (h : n ≤ m) (k : ℕ) : n + k ≤ m + k := by
  rw [add_commutative n k, add_commutative m k]
  exact add_left_less_equal h k
    
theorem add_left_less_than {m k : ℕ} (h : m < k) (n : ℕ) : n + m < n + k := by
  have := add_left_less_equal (successor_less_equal_of_less_than h) n
  apply less_than_of_successor_less_equal
  calc
    successor (n + m) = n + successor m := (add_successor _ _).symm
    _ ≤ n + k := this

theorem add_right_less_than {n m : ℕ} (h : n < m) (k : ℕ) : n + k < m + k := by
  rw [add_commutative n k, add_commutative m k]
  exact add_left_less_than h k

theorem less_equal_of_add_left_less_equal {n m k : ℕ} (h : n + m ≤ n + k) : m ≤ k :=
  let ⟨a, (ha : (n + m) + a = n + k)⟩ := h
  have := calc
    n + (m + a) = (n + m) + a := (add_associative n m a).symm
    _           = n + k       := ha
  Exists.intro a (add_left_cancel this)

theorem less_equal_of_add_right_less_equal {n m k : ℕ} (h : n + k ≤ m + k) : n ≤ m := by
  rw [add_commutative n k, add_commutative m k] at h 
  exact less_equal_of_add_left_less_equal h
  
theorem less_than_of_add_left_less_than {n m k : ℕ} (h : n + m < n + k) : m < k :=
  have := calc
    n + successor m = successor (n + m) := add_successor _ _
    _ ≤ n + k := successor_less_equal_of_less_than h
  less_than_of_successor_less_equal (less_equal_of_add_left_less_equal this)

theorem less_than_of_add_right_less_than {n m k : ℕ} (h : n + k < m + k) : n < m := by
  rw [add_commutative n k, add_commutative m k] at h 
  exact less_than_of_add_left_less_than h

theorem equal_add_positive_of_less_than {n m : ℕ} (h : n < m) : 
  ∃ (a : ℕ), a ≠ 0 ∧ n + a = m := by
  let ⟨a, (ha : (successor n) + a = m)⟩ := successor_less_equal_of_less_than h
  apply Exists.intro (successor a)
  apply And.intro
  . exact successor_not_equal_zero a
  . calc
      n + (successor a) = successor (n + a) := add_successor _ _
      _                 = (successor n) + a := (successor_add _ _).symm
      _                 = m                 := ha

theorem less_than_of_equal_add_positive {n m a : ℕ} : a ≠ 0 → n + a = m → n < m := by
  intro a_not_zero ha
  let ⟨b, (hb : successor b = a), _⟩ := (unique_predecessor_of_positive a_not_zero)
  have := calc
    successor n + b = successor (n + b) := successor_add _ _
    _ = n + successor b := (add_successor _ _ ).symm
    _ = n + a := congrArg (_ + .) hb
    _ = m := ha
  exact less_than_of_successor_less_equal (Exists.intro b this)

theorem left_greater_equal_of_add_right_less_equal {n m k l : ℕ} : n + m = k + l → m ≤ l → n ≥ k := by
  intro h_equal ⟨a, (ha : m + a = l)⟩
  apply Exists.intro a
  apply add_left_cancel (n := m)
  rw [add_left_commutative, ha, ← h_equal, add_commutative]
  
theorem right_greater_equal_of_add_left_less_equal {n m k l : ℕ} : n + m = k + l → n ≤ k → m ≥ l := by
  intro h_equal h_less_equal
  rw [add_commutative n m, add_commutative k l] at h_equal
  exact left_greater_equal_of_add_right_less_equal h_equal h_less_equal

def multiply : ℕ → ℕ → ℕ
  | zero, _ => 0
  | successor n, m => (multiply n m) + m

instance : Mul Natural where
  mul := multiply

@[simp] theorem multiply_definition : multiply n m = n * m := rfl

@[simp] theorem zero_multiply (n : ℕ) : 0 * n = 0 := rfl

theorem successor_multiply (n m : ℕ) : (successor n) * m = (n * m) + m := rfl

@[simp] theorem multiply_zero (n : ℕ) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | successor n ih =>
    calc
      (successor n) * 0 = (n * 0) + 0 := successor_multiply n 0
      _                 = n * 0       := add_zero (n * 0)
      _                 = 0           := ih

theorem multiply_successor (n m : ℕ) : n * (successor m) = (n * m) + n := by
  induction n with
  | zero => rfl
  | successor n ih =>
    show (successor n) * (successor m) = ((successor n) * m) + (successor n)
    calc
      (successor n) * (successor m)
        = n * (successor m) + (successor m)   := successor_multiply n (successor m)
      _ = ((n * m) + n) + (successor m)       := congrArg (. + successor m) ih
      _ = (n * m) + (n + (successor m))       := add_associative (n * m) n (successor m)
      _ = (n * m) + successor (n + m)         := congrArg (n * m + .) (add_successor n m)
      _ = (n * m) + ((successor n) + m)       := congrArg (n * m + .) (successor_add n m).symm
      _ = (n * m) + (m + (successor n))       := congrArg (n * m + .) (add_commutative (successor n) m)
      _ = ((n * m) + m) + (successor n)       := (add_associative (n * m) m (successor n)).symm
      _ = ((successor n) * m) + (successor n) := congrArg (. + (successor n)) (successor_multiply n m).symm

theorem multiply_commutative (n m : ℕ) : n * m = m * n := by
  induction n with
  | zero =>
    calc
      0 * m = 0     := zero_multiply m
      _     = m * 0 := (multiply_zero m).symm
  | successor n ih =>
    calc
      (successor n) * m = (n * m) + m       := successor_multiply n m
      _                 = (m * n) + m       := congrArg (. + m) ih
      _                 = m * (successor n) := (multiply_successor m n).symm

theorem left_distributive (n m k : ℕ) : n * (m + k) = n * m + n * k := by
  induction k with
  | zero => calc
    n * (m + 0) = n * m         := congrArg (n * .) (add_zero m)
    _           = n * m + 0     := (add_zero (n * m)).symm
    _           = n * m + n * 0 := congrArg ((n * m) + .) (multiply_zero n).symm
  | successor k ih => calc
    n * (m + successor k)
      = n * successor (m + k)     := congrArg (n * .) (add_successor m k)
    _ = (n * (m + k)) + n         := multiply_successor n (m + k)
    _ = (n * m + n * k) + n       := congrArg (. + n) ih
    _ = n * m + (n * k + n)       := add_associative (n * m) (n * k) n
    _ = n * m + n * (successor k) := congrArg (n * m + .) (multiply_successor n k).symm

theorem right_distributive (n m k : ℕ) : (n + m) * k = n * k + m * k := by
  calc
    (n + m) * k = k * (n + m)   := multiply_commutative (n + m) k
    _           = k * n + k * m := left_distributive k n m
    _           = n * k + k * m := congrArg (. + k * m) (multiply_commutative k n)
    _           = n * k + m * k := congrArg (n * k + .) (multiply_commutative k m)

theorem multiply_associative (n m k : ℕ) : (n * m) * k = n * (m * k) := by
  induction n with
  | zero => calc
    (0 * m) * k = 0 * k       := congrArg (. * k) (zero_multiply m)
    _           = 0           := zero_multiply k
    _           = 0 * (m * k) := (zero_multiply (m * k)).symm
  | successor n ih => calc
    (successor n * m) * k
      = (n * m + m) * k       := congrArg (. * k) (successor_multiply n m)
    _ = ((n * m) * k) + m * k := right_distributive (n * m) m k
    _ = (n * (m * k)) + m * k := congrArg (. + m * k) ih
    _ = successor n * (m * k) := successor_multiply n (m * k)

@[simp] theorem one_multiply (n : ℕ) : 1 * n = n := rfl

@[simp] theorem multiply_one (n : ℕ) : n * 1 = n := (multiply_commutative n 1).trans (one_multiply n)

theorem equal_zero_of_multiply_equal_zero {n m : ℕ} : n * m = 0 → n = 0 ∨ m = 0 :=
  match n with
  | zero => λ _ => Or.inl rfl
  | successor n =>
    λ h =>
    have h₁ : (n * m) + m = 0 := (successor_multiply n m).symm.trans h
    have h₂ : (n * m) = 0 ∧ m = 0 := equal_zero_of_add_equal_zero h₁
    Or.inr h₂.right

theorem multiply_equal_zero_of_equal_zero {n m : ℕ} : n = 0 ∨ m = 0 → n * m = 0 := by
  intro h
  cases h with
  | inl n_equal_zero => calc
    n * m = 0 * m := congrArg (. * m) n_equal_zero
    _     = 0     := zero_multiply m
  | inr m_equal_zero => calc
    n * m = n * 0 := congrArg (n * .) m_equal_zero
    _     = 0     := multiply_zero n

theorem positive_of_multiply_positive {n m : ℕ} (h : n * m ≠ 0) : n ≠ 0 ∧ m ≠ 0 :=
  have : ¬(n = 0 ∨ m = 0) := mt multiply_equal_zero_of_equal_zero h
  not_or.mp this

theorem multiply_positive_of_positive {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) : n * m ≠ 0 :=
  have : ¬(n = 0 ∨ m = 0) := not_or.mpr (And.intro hn hm)
  mt equal_zero_of_multiply_equal_zero this

theorem multiply_left_commutative (n m k : ℕ) : n * (m * k) = m * (n * k) := by
  rw [← multiply_associative, multiply_commutative n m, multiply_associative]

theorem multiply_right_commutative (n m k : ℕ) : (n * m) * k = (n * k) * m := by
  rw [multiply_associative, multiply_commutative m k, ← multiply_associative]

theorem multiply_left_less_than {m k : ℕ} (h_less_than : m < k) (n : ℕ) (hn_positive : n ≠ 0) : n * m < n * k := by
  let ⟨a, ⟨(ha_positive : a ≠ 0), (h_exists : m + a = k)⟩⟩ := equal_add_positive_of_less_than h_less_than
  apply less_than_of_equal_add_positive
  . show n * a ≠ 0
    exact multiply_positive_of_positive hn_positive ha_positive
  . calc
    n * m + n * a = n * (m + a) := (left_distributive n m a).symm
    _             = n * k       := congrArg (n * .) h_exists

theorem multiply_left_cancel {n m k : ℕ} (h_equal : n * m = n * k) (h_positive : n ≠ 0) : m = k :=
  match less_than_trichotomous m k with
  | Or.inl h_less_than =>
    have : n * m ≠ n * k := not_equal_of_less_than (multiply_left_less_than h_less_than n h_positive)
    absurd h_equal this
  | Or.inr (Or.inl h_equal) => h_equal
  | Or.inr (Or.inr h_greater_than) =>
    have : n * k ≠ n * m := not_equal_of_less_than (multiply_left_less_than h_greater_than n h_positive)
    absurd h_equal this.symm

theorem multiply_right_cancel {n m k : ℕ} (h_equal : n * k = m * k) (h_positive : k ≠ 0) : n = m :=
  have := calc
    k * n = n * k := multiply_commutative k n
    _     = m * k := h_equal
    _     = k * m := multiply_commutative m k
  multiply_left_cancel this h_positive

-- TODO: Fully understand the recursion chapter before messing with this again
--
theorem divideWithRemainder_foo {n m : ℕ} : 0 < m ∧ m ≤ n → distance n m < n :=
  sorry

def divideWithRemainder (n m : ℕ) (hm : m ≠ 0) : ℕ × ℕ :=
  if 0 < m ∧ m ≤ n
  then 
    have : distance n m < n := sorry
    let ⟨q', r'⟩ := (divideWithRemainder (distance n m) m hm)
    ⟨q' + 1, r'⟩
  else ⟨0, n⟩
termination_by divideWithRemainder n m _ => n
--

 
theorem quotient_remainder {n q : ℕ} (q_positive : q ≠ 0) :
  ∃ (p : ℕ × ℕ),
  let ⟨m, r⟩ := p; n = m * q + r ∧ r < q := by
  induction n with
  | zero =>
    apply Exists.intro ⟨0, 0⟩
    apply And.intro
    . calc
      0 = 0 * q := (zero_multiply q).symm
      _ = (0 * q) + 0 := (add_zero (0 * q)).symm
    . have h_exists : 0 + q = q := zero_add q
      exact less_than_of_equal_add_positive q_positive h_exists
  | successor n ih =>
    let ⟨⟨m, r⟩, ⟨(h_exists : n = m * q + r), (h_less_than : r < q)⟩⟩ := ih
    show ∃ p, let ⟨m, r⟩ := p; successor n = m * q + r ∧ r < q
    have : successor r = q ∨ successor r < q := 
      (Or.commutative.mp ∘ less_than_or_equal_of_less_equal ∘ successor_less_equal_of_less_than) h_less_than
    cases this with
    | inl h_equal => 
      apply Exists.intro ⟨successor m, 0⟩
      apply And.intro
      . calc
          successor n = successor (m * q + r)         := congrArg successor h_exists
          _           = m * q + successor r           := (add_successor (m * q) r).symm
          _           = m * successor r + successor r := congrArg (m * . + successor r) h_equal.symm
          _           = successor m * successor r     := (successor_multiply m (successor r)).symm
          _           = successor m * q               := congrArg (successor m * .) h_equal
          _           = successor m * q + 0           := (add_zero (successor m * q)).symm
      . exact zero_less_than_positive q_positive
    | inr h_less_than =>
      apply Exists.intro ⟨m, successor r⟩
      apply And.intro
      . calc
          successor n = successor (m * q + r) := congrArg successor h_exists
          _ = m * q + successor r := (add_successor (m * q) r).symm
      . exact h_less_than

def power (m : ℕ) : ℕ → ℕ
| 0 => 1
| successor n => (power m n) * m

instance : Pow Natural Natural where
  pow := power
