import Barb.Logic

inductive Natural where
  | zero : Natural
  | successor : Natural → Natural

namespace Natural

open Natural (zero successor)

def nat_to_natural (n : Nat) : Natural :=
  match n with
  | Nat.zero => Natural.zero
  | Nat.succ n' => Natural.successor (nat_to_natural n')

instance : OfNat Natural n where
  ofNat := nat_to_natural n

notation "ℕ" => Natural

theorem successor_not_equal_zero (n : ℕ) : successor n ≠ 0 :=
  Natural.noConfusion

theorem successor_injective {n m : ℕ} : successor n = successor m → n = m :=
  λ h => (Natural.noConfusion h) id

theorem successor_not_equal_self (n : ℕ) : successor n ≠ n :=
  Natural.rec 
    (successor_not_equal_zero 0) 
    (λ _ ih => λ h => ih (successor_injective h))
    n

def booleanEqual : ℕ → ℕ → Bool
  | zero, zero => true
  | successor _, zero => false
  | zero, successor _ => false
  | successor n, successor m => booleanEqual n m

instance : BEq Natural where
  beq := booleanEqual

theorem equal_of_boolean_equal_true : {n m : ℕ} → (booleanEqual n m) = true → n = m
  | zero, zero, _ => rfl
  | zero, successor _, h => Bool.noConfusion h
  | successor _, zero, h => Bool.noConfusion h
  | successor _, successor _, h => 
    congrArg successor (equal_of_boolean_equal_true h)

theorem not_equal_of_boolean_equal_false : {n m : ℕ} → (booleanEqual n m) = false → n ≠ m
  | zero, zero, h => Bool.noConfusion h
  | zero, successor x, _ => (successor_not_equal_zero x).symm
  | successor x, zero, _ => successor_not_equal_zero x
  | successor _, successor _, h => 
    mt successor_injective (not_equal_of_boolean_equal_false h)

def decideEqual (n m : ℕ) : Decidable (n = m) :=
  match h : booleanEqual n m with
  | true => isTrue (equal_of_boolean_equal_true h)
  | false => isFalse (not_equal_of_boolean_equal_false h)

@[inline] instance : DecidableEq Natural := decideEqual

def add (n m : ℕ) : ℕ :=
  match n with
  | zero => m
  | successor n' => successor (add n' m)

instance : Add Natural where
  add := add

theorem zero_add (n : ℕ) : 0 + n = n := rfl

theorem successor_add (n m : ℕ) : (successor n) + m = successor (n + m) := rfl

theorem add_zero (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => exact zero_add 0
  | successor x ih => calc
    (successor x) + 0 = successor (x + 0) := successor_add x 0
    _                 = successor x       := congrArg successor ih

theorem add_successor (n m : ℕ) : n + (successor m) = successor (n + m) := by
  induction n with
  | zero => calc
    0 + (successor m) = successor m       := zero_add (successor m)
    _                 = successor (0 + m) := congrArg successor (zero_add m)
  | successor x ih => calc
    (successor x) + (successor m) = successor (x + (successor m)) := successor_add x (successor m)
    _                             = successor (successor (x + m)) := congrArg successor ih

theorem add_commutative (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero => calc
    0 + m = m     := zero_add m
    _     = m + 0 := (add_zero m).symm
  | successor x ih => calc
    (successor x) + m = successor (x + m) := successor_add x m
    _                 = successor (m + x) := congrArg successor ih
    _                 = m + (successor x) := (add_successor m x).symm

theorem add_associative (n m k : ℕ) : (n + m) + k = n + (m + k) := by
  induction n with
  | zero => calc
    (0 + m) + k = m + k       := congrArg (. + k) (zero_add m)
    _           = 0 + (m + k) := zero_add (m + k)
  | successor x ih => calc
    ((successor x) + m) + k = (successor (x + m)) + k := congrArg (. + k) (successor_add x m)
    _                       = successor ((x + m) + k) := successor_add (x + m) k
    _                       = successor (x + (m + k)) := congrArg successor ih

theorem add_left_cancel {n m k : ℕ} : n + m = n + k → m = k := by
  induction n with
  | zero => 
    intro h
    calc
      m = 0 + m := zero_add m
      _ = 0 + k := h
      _ = k     := zero_add k
  | successor x ih =>
    intro h
    have := calc
      successor (x + m) = (successor x) + m := (successor_add x m).symm
      _                 = (successor x) + k := h
      _                 = successor (x + k) := successor_add x k
    exact ih (successor_injective this)

def positive (n : ℕ) : Prop := n ≠ 0

theorem add_positive {n m : ℕ} : positive n → positive (n + m) := by
  cases n with
  | zero => intro h; exact False.elim (h rfl)
  | successor x => intro; exact successor_not_equal_zero (x + m)

theorem equal_zero_of_not_positive {n : ℕ} : ¬(positive n) → n = 0 := by
  cases n with
  | zero => intro; rfl
  | successor x => intro h; exact False.elim (h (successor_not_equal_zero x))
  
theorem not_positive_of_equal_zero {n : ℕ} : n = 0 → ¬(positive n) := by
  cases n with
  | zero => intro _ h; exact False.elim (h rfl)
  | successor x => intro h; exact False.elim (successor_not_equal_zero x h)

theorem equal_zero_of_add_equal_zero {n m : ℕ} : n + m = 0 → (n = 0 ∧ m = 0) := by
  intro h
  apply And.intro
  exact equal_zero_of_not_positive (mt add_positive (not_positive_of_equal_zero h))
  have : m + n = 0 := (add_commutative n m).symm.trans h
  exact equal_zero_of_not_positive (mt add_positive (not_positive_of_equal_zero this))

theorem unique_predecessor_of_positive {n : ℕ} : positive n → ∃! (m : ℕ), successor m = n := by
  cases n with
  | zero => intro h; exact False.elim (h rfl)
  | successor x => intro; exact ExistsUnique.introduction x rfl (λ _ => successor_injective)

def less_equal (n m : ℕ) : Prop := ∃ (a : ℕ), n + a = m

instance : LE Natural where
  le := less_equal

def less_than (n m : ℕ) : Prop := less_equal n m ∧ n ≠ m

instance : LT Natural where
  lt := less_than

theorem less_equal_reflexive (n : ℕ) : n ≤ n := Exists.intro 0 (add_zero n)

theorem less_equal_transitive {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) : n ≤ k := by
  let ⟨x, (h₃ : n + x = m)⟩ := h₁
  let ⟨y, (h₄ : m + y = k)⟩ := h₂
  show ∃ (z : ℕ), n + z = k
  let z := (x + y)
  apply Exists.intro z
  calc
    n + z = n + (x + y) := rfl
    _     = (n + x) + y := (add_associative n x y).symm
    _     = m + y       := congrArg (. + y) h₃
    _     = k           := h₄

instance : Trans less_equal less_equal less_equal where
  trans := less_equal_transitive

theorem less_equal_antisymmetric {n m : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  let ⟨x, (h₃ : n + x = m)⟩ := h₁
  let ⟨y, (h₄ : m + y = n)⟩ := h₂

  suffices x + y = 0 by calc
    n = n + 0 := (add_zero n).symm
    _ = n + x := congrArg (n + .) (equal_zero_of_add_equal_zero this).left.symm
    _ = m     := h₃

  have := calc
    n + 0 = n           := add_zero n
    _     = m + y       := h₄.symm
    _     = (n + x) + y := congrArg (. + y) h₃.symm
    _     = n + (x + y) := add_associative n x y
  show x + y = 0
  exact add_left_cancel this.symm

instance : Antisymm (. ≤ . : ℕ → ℕ → Prop) where
  antisymm := less_equal_antisymmetric

theorem less_than_irreflexive (n : ℕ) : ¬(n < n) := by
  intro h
  have : n ≠ n := h.right
  exact False.elim (this rfl)

theorem less_than_asymmetric (n m : ℕ) : n < m → ¬(n > m) := by
  intro h₁ h₂
  suffices n = m by
  { let ⟨_, (h_not_equal : n ≠ m)⟩ := h₁
    exact absurd this h_not_equal }
    
  let ⟨⟨a, (h₁_exists : n + a = m)⟩, _⟩ := h₁
  let ⟨⟨b, (h₂_exists : m + b = n)⟩, _⟩ := h₂
  have := calc
    n + (a + b) = (n + a) + b := (add_associative n a b).symm
    _           = m + b       := congrArg (. + b) h₁_exists
    _           = n           := h₂_exists
    _           = n + 0       := (add_zero n).symm
  have : a + b = 0 := add_left_cancel this
  calc
    n = n + 0 := (add_zero n).symm
    _ = n + a := congrArg (n + .) (equal_zero_of_add_equal_zero this).left.symm
    _ = m     := h₁_exists

theorem less_than_transitive {n m k : ℕ} (h₁ : n < m) (h₂ : m < k) : n < k := by
  apply And.intro
  . exact less_equal_transitive h₁.left h₂.left
  . intro h_equal
    let ⟨⟨a, (h₁_exists : n + a = m)⟩, h₁_not_equal⟩ := h₁
    let ⟨⟨b, (h₂_exists : m + b = k)⟩, _⟩ := h₂
    have := calc
      n + (a + b) = (n + a) + b := (add_associative n a b).symm
      _           = m + b       := congrArg (. + b) h₁_exists
      _           = k           := h₂_exists
      _           = n           := h_equal.symm
      _           = n + 0       := (add_zero n).symm
    have : a + b = 0 := add_left_cancel this
    have : n = m := calc
      n = n + 0 := (add_zero n).symm
      _ = n + a := congrArg (n + .) (equal_zero_of_add_equal_zero this).left.symm
      _ = m     := h₁_exists
    exact False.elim (h₁_not_equal this)

theorem add_left_less_equal {m k : ℕ} (h : m ≤ k) (n : ℕ) : n + m ≤ n + k := by
  let ⟨x, (h₁ : m + x = k)⟩ := h
  apply Exists.intro x
  calc
    n + m + x = n + (m + x) := add_associative n m x
    _         = n + k       := congrArg (n + .) h₁

theorem add_right_less_equal {n m : ℕ} (h : n ≤ m) (k : ℕ) : n + k ≤ m + k := by
  calc
    n + k = k + n := add_commutative n k
    _     ≤ k + m := add_left_less_equal h k
    _     = m + k := add_commutative k m

theorem less_equal_of_add_left_less_equal {n m k : ℕ} (h : n + m ≤ n + k) : m ≤ k := by
  let ⟨x, (h₁ : n + m + x = n + k)⟩ := h
  have := calc
    n + (m + x) = (n + m) + x := (add_associative n m x).symm
    _           = n + k       := h₁
  show ∃ (x : ℕ), m + x = k
  exact Exists.intro x (add_left_cancel this)

theorem less_equal_of_add_right_less_equal {n m k : ℕ} (h : n + k ≤ m + k) : n ≤ m := by
  have := calc
    k + n = n + k := add_commutative k n
    _     ≤ m + k := h
    _     = k + m := add_commutative m k
  exact less_equal_of_add_left_less_equal this

theorem less_than_of_successor_less_equal {n m : ℕ} (h : successor n ≤ m) : n < m := by
  let ⟨x, (h₁ : (successor n) + x = m)⟩ := h
  have h₂ := calc
    n + (successor x) = successor (n + x) := add_successor n x
    _                 = (successor n) + x := (successor_add n x).symm
    _                 = m                 := h₁
  apply And.intro
  . exact (Exists.intro (successor x) h₂)
  . show n ≠ m
    intro (h₃ : n = m)
    have := calc
      n + (successor x) = m     := h₂
      _                 = n     := h₃.symm
      _                 = n + 0 := (add_zero n).symm
    exact successor_not_equal_zero x (add_left_cancel this)

theorem successor_less_equal_of_less_than : {n m : ℕ} → n < m → successor n ≤ m
| zero, zero, ⟨_, h⟩ => False.elim (h rfl)
| zero, successor y, _ => by
  apply Exists.intro y
  calc
    successor zero + y = successor (zero + y) := successor_add zero y
    _                  = successor y          := congrArg successor (zero_add y)
| successor x, zero, ⟨h, _⟩ => by
  let ⟨z, (h₁ : (successor x) + z = zero)⟩ := h
  have : successor (x + z) = 0 := (successor_add x z).symm.trans h₁
  exact False.elim (successor_not_equal_zero (x + z) this)
| successor x, successor y, ⟨h₁, h₂⟩ => by
  show successor (successor x) ≤ successor y
  
  suffices h₃ : x ≤ y ∧ x ≠ y by
  { let ⟨w, (h₄ : (successor x) + w = y)⟩ := successor_less_equal_of_less_than h₃
    have := calc
      (successor (successor x)) + w = successor (successor x + w) := successor_add (successor x) w
      _                             = successor y                 := congrArg successor h₄
    exact Exists.intro w this }

  let ⟨z, (h₄ : successor x + z = successor y)⟩ := h₁
  apply And.intro
  . have h₅ := calc
      successor (x + z) = (successor x) + z := (successor_add x z).symm
      _                 = successor y       := h₄
    exact Exists.intro z (successor_injective h₅)
  . exact mt (congrArg successor) h₂

theorem equal_add_positive_of_less_than {n m : ℕ} (h : n < m) : 
  ∃ (a : ℕ), positive a ∧ n + a = m := by
  let ⟨b, (h₁ : (successor n) + b = m)⟩ := successor_less_equal_of_less_than h
  apply Exists.intro (successor b)
  apply And.intro
  . exact successor_not_equal_zero b
  . calc
      n + (successor b) = successor (n + b) := add_successor n b
      _                 = (successor n) + b := (successor_add n b).symm
      _                 = m                 := h₁

theorem less_than_of_equal_add_positive {n m : ℕ} 
  (h : ∃ (a : ℕ), positive a ∧ n + a = m) : n < m := by
  let ⟨a, (h₁ : positive a), (h₂ : n + a = m)⟩ := h
  let ⟨b, (h₃ : successor b = a), _⟩ := (unique_predecessor_of_positive h₁)
  apply And.intro
  . exact Exists.intro a h₂
  . intro (h₄ : n = m)
    have := calc
      n + (successor b) = n + a := congrArg (n + .) h₃
      _                 = m     := h₂
      _                 = n     := h₄.symm
      _                 = n + 0 := (add_zero n).symm
    exact successor_not_equal_zero b (add_left_cancel this)

theorem less_than_trichotomous (n m : ℕ) : n < m ∨ n = m ∨ n > m := by
  induction n with
  | zero => cases m with
    | zero => exact Or.inr (Or.inl rfl)
    | successor y =>
      apply Or.inl
      apply And.intro
      . exact Exists.intro (successor y) (zero_add (successor y))
      . exact (successor_not_equal_zero y).symm
  | successor x ihl =>
      cases ihl with
      | inl h_less_than =>
        let ⟨a, (h₁ : (successor x) + a = m)⟩ := successor_less_equal_of_less_than h_less_than
        cases a with
        | zero =>
          apply Or.inr
          apply Or.inl
          exact calc
            (successor x) = (successor x) + 0 := (add_zero (successor x)).symm
            _             = m                 := h₁
        | successor a' =>
          apply Or.inl
          apply less_than_of_equal_add_positive
          apply Exists.intro (successor a')
          apply And.intro
          . exact successor_not_equal_zero a'
          . exact h₁
      | inr ihr => cases ihr with
        | inl h_equal =>
          apply Or.inr; apply Or.inr;
          apply less_than_of_equal_add_positive
          apply Exists.intro 1
          apply And.intro
          . exact successor_not_equal_zero 0
          . exact calc
              m + 1 = successor (m + 0) := add_successor m 0
              _     = successor m       := congrArg successor (add_zero m)
              _     = successor x       := congrArg successor h_equal.symm
        | inr h_greater_than =>
          let ⟨a, (h₁ : m + a = x)⟩ := h_greater_than.left
          apply Or.inr; apply Or.inr;
          have := calc
            m + (successor a) = successor (m + a) := add_successor m a
            _                 = successor x := congrArg successor h₁
          apply less_than_of_equal_add_positive
          apply Exists.intro (successor a)
          apply And.intro
          . exact successor_not_equal_zero a
          . exact this

def multiply (n m : ℕ) : ℕ :=
  match n with
  | zero => 0
  | successor n' => (multiply n' m) + m

instance : Mul Natural where
  mul := multiply

theorem zero_multiply (n : ℕ) : 0 * n = 0 := rfl

theorem successor_multiply (n m : ℕ) : (successor n) * m = (n * m) + m := rfl

theorem multiply_zero (n : ℕ) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | successor x ih =>
    exact calc
      (successor x) * 0 = (x * 0) + 0 := successor_multiply x 0
      _                 = x * 0       := add_zero (x * 0)
      _                 = 0           := ih

theorem multiply_successor (n m : ℕ) : n * (successor m) = (n * m) + n := by
  induction n with
  | zero => rfl
  | successor x ih => 
    show (successor x) * (successor m) = ((successor x) * m) + (successor x)
    exact calc
      (successor x) * (successor m)
        = x * (successor m) + (successor m)   := successor_multiply x (successor m)
      _ = ((x * m) + x) + (successor m)       := congrArg (. + successor m) ih
      _ = (x * m) + (x + (successor m))       := add_associative (x * m) x (successor m)
      _ = (x * m) + successor (x + m)         := congrArg (x * m + .) (add_successor x m)
      _ = (x * m) + ((successor x) + m)       := congrArg (x * m + .) (successor_add x m).symm
      _ = (x * m) + (m + (successor x))       := congrArg (x * m + .) (add_commutative (successor x) m)
      _ = ((x * m) + m) + (successor x)       := (add_associative (x * m) m (successor x)).symm
      _ = ((successor x) * m) + (successor x) := congrArg (. + (successor x)) (successor_multiply x m).symm

theorem multiply_commutative (n m : ℕ) : n * m = m * n := by
  induction n with
  | zero =>
    exact calc
      0 * m = 0     := zero_multiply m
      _     = m * 0 := (multiply_zero m).symm
  | successor n ih =>
    exact calc
      (successor n) * m = (n * m) + m       := successor_multiply n m
      _                 = (m * n) + m       := congrArg (. + m) ih
      _                 = m * (successor n) := (multiply_successor m n).symm

theorem equal_zero_of_multiply_equal_zero (n m : ℕ) : n * m = 0 → n = 0 ∨ m = 0 := by
  cases n with
  | zero =>
    intro _
    exact Or.inl rfl
  | successor n =>
    intro h
    have h₁ : (n * m) + m = 0 := (successor_multiply n m).symm.trans h
    have h₂ : (n * m) = 0 ∧ m = 0 := equal_zero_of_add_equal_zero h₁
    exact Or.inr h₂.right

theorem multiply_equal_zero_of_equal_zero (n m : ℕ) : n = 0 ∨ m = 0 → n * m = 0 := by
  intro h
  cases h with
  | inl n_equal_zero => exact calc
    n * m = 0 * m := congrArg (. * m) n_equal_zero
    _     = 0     := zero_multiply m
  | inr m_equal_zero => exact calc
    n * m = n * 0 := congrArg (n * .) m_equal_zero
    _     = 0     := multiply_zero n
