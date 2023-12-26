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
def six : ℕ := successor (successor (successor (successor (successor (successor zero)))))
def two : ℕ := successor (successor zero)

example : six ≠ two :=
  λ h : 6 = 2 =>
  let h1 := successor_injective 5 1 h;
  let h2 := successor_injective 4 0 h1;
  successor_not_equal_zero 3 h2

-- Axiom 2.5 we get baked in as the recursor

/-
Okay so the trying to replace Init thing was stupid, but I did learn a few things:

- The elimination rule for False, that you can prove anything from a 
contradiction, just pops out of the normal scheme for recursors. Beautiful!

- How to do prove things using Not. Just treat if like any other function to 
produce an "element" of False.
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

instance : Add Natural where
  add := Natural.add

example : (2 : Natural) + (5 : Natural) = (7 : Natural) := rfl

-- macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command => `($mods:declModifiers theorem $n $sig $val)

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
    show (successor x) + m = m + (successor x) from h1.trans (h3.trans (h2.symm))
    )
    n


end Natural
