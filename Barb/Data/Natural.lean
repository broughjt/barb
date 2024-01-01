import Barb.Logic

inductive Natural where
  -- Axiom 2.1
  | zero : Natural
  -- Axiom 2.2
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

/-
https://github.com/leanprover/lean4/blob/b614ff1d12bc38f39077f9ce9f2d48b42c003ad0/src/Init/Data/Nat/Basic.lean#L432-L433

Axiom 2.3
-/
theorem successor_not_equal_zero (n : ℕ) : successor n ≠ 0 :=
  Natural.noConfusion

/-
Absolutely no idea why the type for Natural.noConfusionType or what I've written 
means. It works and for now I'm going to move on

variable (m n : Natural)
variable (P : Sort u)

#reduce Natural.noConfusionType P (successor m) (successor n)

Axiom 2.4
-/
theorem successor_injective (m n : ℕ) : successor m = successor n → m = n :=
  λ h => (Natural.noConfusion h) id

/-
TODO: How to tidy up?
-/
example : (6 : ℕ) ≠ 2 :=
  λ h : 6 = 2 =>
  let h1 := successor_injective 5 1 h;
  let h2 := successor_injective 4 0 h1;
  successor_not_equal_zero 3 h2

-- Axiom 2.5 we get baked in as the recursor

/-
Okay so the trying to replace Init thing was stupid, but I did learn a few things:

- The elimination rule for False -- that you can prove anything from a 
contradiction -- just pops out of the normal scheme for recursors. Beautiful!

- How to do prove things using Not. Just treat if like any other function to 
produce an "element" of False.

- Familiarity with term-style proofs
-/

/-
TODO: How to do with tactics?
-/
theorem successor_not_equal_self (n : ℕ) : successor n ≠ n :=
  Natural.rec 
    (successor_not_equal_zero 0) 
    (λ x ih => λ h => ih (successor_injective (successor x) x h))
    n

def add (n m : ℕ) : ℕ :=
  match n with
  | zero => m
  | successor n' => successor (add n' m)

/-
Addition is left associative, so `a + b + c` is definitionally equal to `(a + b) + c`.
-/
instance : Add Natural where
  add := add

theorem zero_add (n : ℕ) : 0 + n = n := rfl

theorem successor_add (n m : ℕ) : (successor n) + m = successor (n + m) := rfl

/-
TODO: Simplify: it's big and it's ugly. Figuring out how to use tactics here will 
be a very useful exercise.

I think only h1 and h3 are necessary?

The `have` construct is the same as let

let h1 : p := ...;

is the same as

have h1 : p := ...

(without the semicolon).

The `show` construct just makes types explicit. If we have

x : p,

it is the same as

show p from x
-/
theorem add_zero (n : ℕ) : n + 0 = n := 
  Natural.rec
    (zero_add 0)
    (λ (x : ℕ) (ih : x + 0 = x) =>
    have h1 : (successor x) + 0 = successor (x + 0) := successor_add x 0
    have h2 : successor (x + 0) = (successor x) + 0 := Eq.symm h1
    have h3 : successor x = (successor x) + 0 := 
      Eq.subst (motive := λ a => successor a = (successor x) + 0)
        ih
        h2
    show (successor x) + 0 = successor x from Eq.symm h3)
    n

theorem add_zero' (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => exact zero_add 0
  | successor x ih => calc
    (successor x) + 0 = successor (x + 0) := successor_add x 0
    _                 = successor x       := congrArg successor ih

theorem add_successor (n m : ℕ) : n + (successor m) = successor (n + m) :=
  Natural.rec
    (
    have h1 : 0 + (successor m) = successor m := zero_add (successor m)
    -- congrArg to the rescue!
    have h2 : successor (0 + m) = successor m := congrArg successor (zero_add m)
    show 0 + (successor m) = successor (0 + m) from Eq.trans h1 (Eq.symm h2)
    )
    (λ (x : ℕ) (ih : x + (successor m) = successor (x + m)) =>
    have h1 : (successor x) + (successor m) = successor (x + (successor m)) := successor_add x (successor m)
    have h2 : successor (x + (successor m)) = successor (successor (x + m)) := congrArg successor ih
    -- Little extra help from the compiler since (successor x) + m) is definitionally equal to sucessor (x + m)
    show (successor x) + (successor m) = successor ((successor x) + m) from Eq.trans h1 h2
    )
    n

theorem add_successor' (n m : ℕ) : n + (successor m) = successor (n + m) := by
  induction n with
  | zero => calc
    0 + (successor m) = successor m       := zero_add (successor m)
    _                 = successor (0 + m) := congrArg successor (zero_add m)
  | successor x ih => calc
    (successor x) + (successor m) = successor (x + (successor m)) := successor_add x (successor m)
    _                             = successor (successor (x + m)) := congrArg successor ih

/-
Addition is just a successor swapping game. Computing `n + m` increments m n times. Computing `m + n` increments n m times.
-/
theorem add_commutative (n m : ℕ) : n + m = m + n := 
  Natural.rec
    (
    show 0 + m = m + 0 from Eq.trans (zero_add m) (Eq.symm (add_zero m))
    )
    (λ (x : ℕ) (ih : x + m = m + x) => 
    have h1 : (successor x) + m = successor (x + m) := successor_add x m
    have h2 : m + (successor x) = successor (m + x) := add_successor m x
    have h3 : successor (x + m) = successor (m + x) := congrArg successor ih
    show (successor x) + m = m + (successor x) from h1.trans (h3.trans h2.symm)
    )
    n

theorem add_commutative' (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero => calc
    0 + m = m     := zero_add m
    _     = m + 0 := (add_zero m).symm
  | successor x ih => calc
    (successor x) + m = successor (x + m) := successor_add x m
    _                 = successor (m + x) := congrArg successor ih
    _                 = m + (successor x) := (add_successor m x).symm

example : ((5 : ℕ) + 2) + 4 = 5 + (2 + 4) := rfl

theorem add_associative (a b c : ℕ) : (a + b) + c = a + (b + c) :=
  Natural.rec
    (
    have h1 : (0 + b) + c = b + c := congrArg (λ x => x + c) (zero_add b)
    have h2 : 0 + (b + c) = b + c := zero_add (b + c)
    show (0 + b) + c = 0 + (b + c) from h1.trans h2.symm
    )
    (λ (x : ℕ) (ih : (x + b) + c = x + (b + c)) =>
    have h1 : ((successor x) + b) + c = (successor (x + b)) + c := congrArg (λ y => y + c) (successor_add x b)
    have h2 : (successor (x + b)) + c = successor ((x + b) + c) := successor_add (x + b) c
    have h3 : successor ((x + b) + c) = successor (x + (b + c)) := congrArg successor ih
    have h4 : (successor x) + (b + c) = successor (x + (b + c)) := successor_add x (b + c)
    show ((successor x) + b) + c = (successor x) + (b + c) from (h1.trans h2).trans (h3.trans h4.symm)
    )
    a

theorem add_associative' (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => calc
    (0 + b) + c = b + c       := congrArg (. + c) (zero_add b)
    _           = 0 + (b + c) := zero_add (b + c)
  | successor x ih => calc
    ((successor x) + b) + c = (successor (x + b)) + c := congrArg (. + c) (successor_add x b)
    _                       = successor ((x + b) + c) := successor_add (x + b) c
    _                       = successor (x + (b + c)) := congrArg successor ih

theorem add_left_cancel {a b c : ℕ} : a + b = a + c → b = c := 
  Natural.rec
    (
    have h1 : 0 + b = b := zero_add b
    have h2 : 0 + c = c := zero_add c
    show 0 + b = 0 + c → b = c from (λ h3 => (h1.symm.trans h3).trans h2)
    )
    (λ (x : ℕ) (ih : x + b = x + c → b = c) =>
    have h1 : (successor x) + b = successor (x + b) := successor_add x b
    have h2 : (successor x) + c = successor (x + c) := successor_add x c
    show (successor x) + b = (successor x) + c → b = c from (λ h =>
      have h3 : successor (x + b) = successor (x + c) := (h1.symm.trans h).trans h2
      ih (successor_injective (x + b) (x + c) h3)
    )
    )
    a

theorem add_left_cancel' (a b c : ℕ) : a + b = a + c → b = c := by
  induction a with
  | zero => 
    intro h
    calc
      b = 0 + b := zero_add b
      _ = 0 + c := h
      _ = c     := zero_add c
  | successor x ih =>
    intro h
    have := calc
      successor (x + b) = (successor x) + b := (successor_add x b).symm
      _                 = (successor x) + c := h
      _                 = successor (x + c) := successor_add x c
    exact ih (successor_injective (x + b) (x + c) this)


def positive (n : ℕ) : Prop := n ≠ 0

theorem add_positive (n m : ℕ) : positive n → positive (n + m) :=
  Natural.rec
    (
    show positive 0 → positive (0 + m) 
    from (λ (h : positive 0) => 
    -- Basically call bullshit. If you're telling me 0 ≠ 0, I'm gonna tell you 
    -- that 0 + m for any m is not equal to zero.
    show positive (0 + m) from False.elim (h rfl)
    )
    )
    -- There's some automatic definitional equality simplifying going on here, relies on the definition of addition
    (λ (x : ℕ) _ _ => successor_not_equal_zero (x + m))
    n

theorem add_positive' (n m : ℕ) : positive n → positive (n + m) := by
  cases n with
  | zero => intro h; exact False.elim (h rfl)
  | successor x => intro; exact successor_not_equal_zero (x + m)

-- Clearly we're missing something, proving this "corollary" is too difficult

/- 
TODO: Is there a way to prove this without induction?

It probably has something to do with proving decidable equality for integers.
-/
theorem equal_zero_iff_not_positive (n : ℕ) : ¬(positive n) ↔ n = 0 := 
  Natural.rec
    -- Hmmm, which natural numbers equal zero... zero equals zero.
    (Iff.intro (λ _ => rfl) (λ _ => (λ g => False.elim (g rfl))))
    (λ x _ =>
    (Iff.intro
      (λ h => False.elim (h (successor_not_equal_zero x)))
      (λ h => False.elim (successor_not_equal_zero x h))))
    n

theorem equal_zero_of_not_positive (n : ℕ) : ¬(positive n) → n = 0 := by
  cases n with
  | zero => intro; rfl
  | successor x => intro h; exact False.elim (h (successor_not_equal_zero x))
  
theorem not_positive_of_equal_zero (n : ℕ) : n = 0 → ¬(positive n) := by
  cases n with
  | zero => intro _ h; exact False.elim (h rfl)
  | successor x => intro h; exact False.elim (successor_not_equal_zero x h)

-- Corollary 2.2.9
theorem equal_zero_of_add_equal_zero (n m : ℕ) : n + m = 0 → (n = 0 ∧ m = 0) :=
  λ (h : n + m = 0) => 
    -- Oh my goodness, have to convert on the way in and the way out? Has to be a better way
    have h2 : n = 0 := ((equal_zero_iff_not_positive n).mp (mt (add_positive n m) ((equal_zero_iff_not_positive (n + m)).mpr h)))
    have h3 : m + n = 0 := (add_commutative n m).symm.trans h
    have h4 : m = 0 := ((equal_zero_iff_not_positive m).mp (mt (add_positive m n) ((equal_zero_iff_not_positive (m + n)).mpr h3)))
    show n = 0 ∧ m = 0 from And.intro h2 h4

theorem equal_zero_of_add_equal_zero' (n m : ℕ) : n + m = 0 → (n = 0 ∧ m = 0) := by
  intro h
  apply And.intro
  exact equal_zero_of_not_positive n (mt (add_positive n m) (not_positive_of_equal_zero (n + m) h))
  have : m + n = 0 := (add_commutative n m).symm.trans h
  exact equal_zero_of_not_positive m (mt (add_positive m n) (not_positive_of_equal_zero (m + n) this))
    
-- TODO: If you don't use the inductive hypothesis, isn't that a pretty good sign that you don't need induction?
theorem unique_predecessor_of_positive (n : ℕ) : (positive n) → ∃! (m : ℕ), successor m = n :=
  Natural.rec
    (λ h => False.elim (h rfl))
    (λ x _ _ => 
    have h2 : ∀ y, successor y = successor x → y = x := (λ y => successor_injective y x)
    show ∃! (y : ℕ), successor y = successor x from ExistsUnique.introduction x rfl h2
    )
    n

theorem unique_predecessor_of_positive' (n : ℕ) : positive n → ∃! (m : ℕ), successor m = n := by
  cases n with
  | zero => intro h; exact False.elim (h rfl)
  | successor x => intro; exact ExistsUnique.introduction x rfl (λ y => successor_injective y x)

def booleanEqual : ℕ → ℕ → Bool
  | zero, zero => true
  | successor _, zero => false
  | zero, successor _ => false
  | successor n, successor m => booleanEqual n m
  
instance : BEq Natural where
  beq := booleanEqual

-- theorem equal_of_boolean_equal_true : (n m : ℕ) → (beq n m) = true → n = m := sorry

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
  | successor x, successor y, h => 
    mt (successor_injective x y) (not_equal_of_boolean_equal_false h)

/-
A decision procedure for equality of natural numbers.

I was thinking about what a decision procedure must be while snowboarding today, 
and I think I've got it. A decision procedure takes a predicate of the 
form p : α → Prop and an element of that type a : α, and then "decides" p a by 
providing a proof of p a or a proof of ¬(p a). Giving a decision procedure for a 
predicate p shows that p is "decidable," because given any instance of a, we have 
an algorithm for showing whether p a or not p a.
-/
def decideEqual (n m : ℕ) : Decidable (n = m) :=
  match h : booleanEqual n m with
  | true => isTrue (equal_of_boolean_equal_true h)
  | false => isFalse (not_equal_of_boolean_equal_false h)

@[inline] instance : DecidableEq Natural := decideEqual

def less_equal (n m : ℕ) : Prop := ∃ (a : ℕ), n + a = m

instance : LE Natural where
  le := less_equal

def less_than (n m : ℕ) : Prop := less_equal n m ∧ n ≠ m

instance : LT Natural where
  lt := less_than

theorem less_equal_reflexive (n : ℕ) : n ≤ n := Exists.intro 0 (add_zero n)

-- TODO: Make typeclass instances for reflexive, transitive, and antisymmteric. Classes are already in Init

theorem less_equal_transitive' (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := 
  Exists.elim h₁
  (λ x h3 => 
  Exists.elim h₂
  (λ y h4 =>
  have h5 : a + x + y = c := Eq.subst (motive := (. + y = c)) h3.symm h4
  have h6 : a + (x + y) = c := (add_associative a x y).symm.trans h5
  let z := (x + y)
  have h7 : a + z = c := Eq.subst rfl h6
  Exists.intro z h7))

theorem less_equal_transitive {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  -- TODO: Make it clear what h3 and h4 are, a + x = b, b + y = c
  apply Exists.elim h₁; intro x h₃
  apply Exists.elim h₂; intro y h₄
  show ∃ (z : ℕ), a + z = c
  let z := (x + y)
  apply Exists.intro z
  calc
    a + z = a + (x + y) := rfl
    _     = (a + x) + y := (add_associative a x y).symm
    _     = b + y       := congrArg (. + y) h₃
    _     = c           := h₄

instance : Trans (. ≤ . : ℕ → ℕ → Prop) (. ≤ . : ℕ → ℕ → Prop) (. ≤ . : ℕ → ℕ → Prop) where
  trans := less_equal_transitive

theorem less_equal_antisymmetric {n m : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  apply Exists.elim h₁; intro x h₃
  apply Exists.elim h₂; intro y h₄

  suffices x + y = 0 by calc
    n = n + 0 := (add_zero n).symm
    _ = n + x := congrArg (n + .) (equal_zero_of_add_equal_zero x y this).left.symm
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

theorem add_less_equal_add_left {b c : ℕ} (h : b ≤ c) (a : ℕ) : a + b ≤ a + c := by
  apply Exists.elim h; intro x h₁;
  apply Exists.intro x
  calc
    a + b + x = a + (b + x) := add_associative a b x
    _         = a + c       := congrArg (a + .) h₁

theorem add_less_equal_add_right {a b : ℕ} (h : a ≤ b) (c : ℕ) : a + c ≤ b + c := by
  calc
    a + c = c + a := add_commutative a c
    _     ≤ c + b := add_less_equal_add_left h c
    _     = b + c := add_commutative c b

theorem less_equal_of_add_less_equal_add_left {a b c : ℕ} (h : a + b ≤ a + c) : b ≤ c := by
  apply Exists.elim h; intro x h₁
  have : a + (b + x) = a + c := (add_associative a b x).symm.trans h₁
  exact Exists.intro x (add_left_cancel this)

theorem less_equal_of_add_less_equal_add_right {a b c : ℕ} (h : a + c ≤ b + c) : a ≤ b := by
  have := calc
    c + a = a + c := add_commutative c a
    _     ≤ b + c := h
    _     = c + b := add_commutative b c
  exact less_equal_of_add_less_equal_add_left this

theorem less_than_of_successor_less_equal {a b : ℕ} (h : successor a ≤ b) : a < b := by
  apply Exists.elim h; intro x h₁
  have h₂ := calc
    a + (successor x) = successor (a + x) := add_successor a x
    _                 = (successor a) + x := (successor_add a x).symm
    _                 = b                 := h₁
  apply And.intro
  . exact (Exists.intro (successor x) h₂)
  . show a ≠ b
    intro h₃
    have := calc
      a + (successor x) = b     := h₂
      _                 = a     := h₃.symm
      _                 = a + 0 := (add_zero a).symm
    exact successor_not_equal_zero x (add_left_cancel this)

-- TODO: Is it possible to do this one without induction?
theorem successor_less_equal_of_less_than : {a b : ℕ} → a < b → successor a ≤ b
| zero, zero, ⟨_, h⟩ => False.elim (h rfl)
| zero, successor y, _ => by
  apply Exists.intro y
  calc
    successor zero + y = successor (zero + y) := successor_add zero y
    _                  = successor y := congrArg successor (zero_add y)
| successor x, zero, ⟨h, _⟩ => by
  apply Exists.elim h; intro z h₁
  have : successor (x + z) = 0 := (successor_add x z).symm.trans h₁
  exact False.elim (successor_not_equal_zero (x + z) this)
| successor x, successor y, ⟨h₁, h₂⟩ => by
  show successor (successor x) ≤ successor y
  
  suffices h₃ : x ≤ y ∧ x ≠ y by
  { apply Exists.elim (successor_less_equal_of_less_than h₃); 
    intro w h₄;
    have := calc
      (successor (successor x)) + w = successor (successor x + w) := successor_add (successor x) w
      _                             = successor y                 := congrArg successor h₄
    exact Exists.intro w this }

  apply Exists.elim h₁; intro z h₄
  apply And.intro
  . have h₅ := calc
      successor (x + z) = (successor x) + z := (successor_add x z).symm
      _                 = successor y       := h₄
    exact Exists.intro z (successor_injective (x + z) y h₅)
  . exact mt (congrArg successor) h₂

theorem equal_add_positive_of_less_than {a b : ℕ} (h : a < b) : 
  ∃ (d : ℕ), positive d ∧ a + d = b := by
  apply Exists.elim (successor_less_equal_of_less_than h); intro c h₁
  apply Exists.intro (successor c)
  apply And.intro
  . exact successor_not_equal_zero c
  . calc
      a + (successor c) = successor (a + c) := add_successor a c
      _                 = (successor a) + c := (successor_add a c).symm
      _                 = b                 := h₁

theorem less_than_of_equal_add_positive {a b : ℕ} (h : ∃ (d : ℕ), positive d ∧ a + d = b) : a < b := by
  apply Exists.elim h; intro d ⟨h₁, h₂⟩
  -- TODO: Make first argument of unique_... implicit
  apply Exists.elim (unique_predecessor_of_positive d h₁); intro c h₃
  apply And.intro
  . exact Exists.intro d h₂
  . intro h₄
    have := calc
      a + (successor c) = a + d := congrArg (a + .) h₃.left
      _                 = b     := h₂
      _                 = a     := h₄.symm
      _                 = a + 0 := (add_zero a).symm
    exact successor_not_equal_zero c (add_left_cancel this)

theorem trichotomous (a b : ℕ) : a < b ∨ a = b ∨ a > b := sorry

end Natural
