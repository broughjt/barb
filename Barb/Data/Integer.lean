import Barb.Algebra
import Barb.Data.Natural
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

instance decideIntegerEquivalentQuotientEqual: DecidableEq (Quotient instanceSetoidIntegerEquivalent) := inferInstance

def Integer := Quotient instanceSetoidIntegerEquivalent

instance decideEqual : DecidableEq Integer := decideIntegerEquivalentQuotientEqual

namespace Integer

notation "ℤ" => Integer

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
  have h₃ : (n * k + m * l) + (n' * l + m' * k) = (n' * k + m' * l) + (n * l + m * k) := calc
    (n * k + m * l) + (n' * l + m' * k) = (n * k + m * l) + (m' * k + n' * l) := congrArg (_ + .) (Natural.add_commutative (n' * l) (m' * k))
    _ = n * k + (m * l + (m' * k + n' * l)) := Natural.add_associative (n * k) (m * l) (m' * k + n' * l)
    _ = n * k + ((m * l + m' * k) + n' * l) := congrArg (_ + .) (Natural.add_associative (m * l) (m' * k) (n' * l)).symm
    _ = n * k + ((m' * k + m * l) + n' * l) := congrArg (λ x => (n * k + (x + n' * l))) (Natural.add_commutative (m * l) (m' * k))
    _ = (n * k + (m' * k + m * l)) + n' * l := (Natural.add_associative (n * k) (m' * k + m * l) (n' * l)).symm
    _ = ((n * k + m' * k) + m * l) + n' * l := congrArg (. + _) (Natural.add_associative (n * k) (m' * k) (m * l)).symm
    _ = (n * k + m' * k) + (m * l + n' * l) := Natural.add_associative (n * k + m' * k) (m * l) (n' * l)
    _ = (n + m') * k + (m * l + n' * l) := congrArg (. + _) (Natural.right_distributive n m' k).symm
    _ = (n + m') * k + (m + n') * l := congrArg (_ + .) (Natural.right_distributive m n' l).symm
    _ = (n' + m) * k + (m + n') * l := congrArg (. * _ + _) h₁
    _ = (n' + m) * k + (n + m') * l := congrArg (_ + . * _) ((Natural.add_commutative m n').trans h₁.symm)
    _ = (n' * k + m * k) + (n + m') * l := congrArg (. + _) (Natural.right_distributive n' m k)
    _ = (n' * k + m * k) + (n * l + m' * l) := congrArg (_ + .) (Natural.right_distributive n m' l)
    _ = n' * k + (m * k + (n * l + m' * l)) := Natural.add_associative (n' * k) (m * k) (n * l + m' * l)
    _ = n' * k + ((m * k + n * l) + m' * l) := congrArg (_ + .) (Natural.add_associative (m * k) (n * l) (m' * l)).symm
    _ = n' * k + ((n * l + m * k) + m' * l) := congrArg (λ x => _ + (x + _)) (Natural.add_commutative (m * k) (n * l))
    _ = n' * k + (n * l + (m * k + m' * l)) := congrArg (_ + .) (Natural.add_associative (n * l) (m * k) (m' * l))
    _ = n' * k + (n * l + (m' * l + m * k)) := congrArg (λ x => _ + (_ + x)) (Natural.add_commutative (m * k) (m' * l))
    _ = n' * k + ((n * l + m' * l) + m * k) := congrArg (_ + .) (Natural.add_associative (n * l) (m' * l) (m * k)).symm
    _ = n' * k + ((m' * l + n * l) + m * k) := congrArg (λ x => _ + (x + _)) (Natural.add_commutative (n * l) (m' * l))
    _ = n' * k + (m' * l + (n * l + m * k)) := congrArg (_ + .) (Natural.add_associative (m' * l) (n * l) (m * k))
    _ = (n' * k + m' * l) + (n * l + m * k) := (Natural.add_associative (n' * k) (m' * l) (n * l + m * k)).symm
  show (n * k + m * l) + (n' * l' + m' * k') = (n' * k' + m' * l') + (n * l + m * k)
  have h₄ := calc
    ((n * l + m * k) + (n' * k + m' * l)) + ((n * k + m * l) + (n' * l' + m' * k')) 
    = (n * l + m * k) + ((n' * k + m' * l) + ((n * k + m * l) + (n' * l' + m' * k'))) := Natural.add_associative _ _ _
    _ = (n * l + m * k) + (((n' * k + m' * l) + (n * k + m * l)) + (n' * l' + m' * k')) := congrArg (_ + .) (Natural.add_associative _ _ _).symm
    _ = (n * l + m * k) + (((n * k + m * l) + (n' * k + m' * l)) + (n' * l' + m' * k')) := congrArg (λ x => (_ + (x + _))) (Natural.add_commutative _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + ((n' * k + m' * l) + (n' * l' + m' * k'))) := congrArg (_ + .) (Natural.add_associative _ _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + ((n' * k) + ((m' * l) + (n' * l' + m' * k')))) := congrArg (λ x => (_ + (_ + x))) (Natural.add_associative _ _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + ((n' * k) + (((m' * l) + (n' * l')) + m' * k'))) := congrArg (λ x => (_ + (_ + (_ + x)))) (Natural.add_associative _ _ _).symm
    _ = (n * l + m * k) + ((n * k + m * l) + ((n' * k) + (((n' * l') + (m' * l)) + m' * k'))) := congrArg (λ x => (_ + (_ + (_ + (x + _))))) (Natural.add_commutative _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * k + (n' * l' + (m' * l + m' * k')))) := congrArg (λ x => (_ + (_ + (_ + x)))) (Natural.add_associative _ _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + ((n' * k + n' * l') + (m' * l + m' * k'))) := congrArg (λ x => (_ + (_ + x))) (Natural.add_associative _ _ _).symm
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * (k + l') + (m' * l + m' * k'))) := congrArg (λ x => (_ + (_ + (x + _)))) (Natural.left_distributive _ _ _).symm
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * (k + l') + m' * (l + k'))) := congrArg (λ x => (_ + (_ + (_ + x)))) (Natural.left_distributive _ _ _).symm
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * (k' + l) + m' * (l + k'))) := congrArg (λ x => (_ + (_ + (_ * x + _)))) h₂ 
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * (k' + l) + m' * (k' + l))) := congrArg (λ x => _ + (_ + (_ * _ + _ * x))) (Natural.add_commutative _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * (k' + l) + m' * (k + l'))) := congrArg (λ x => _ + (_ + (_ * _ + _ * x))) h₂.symm
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * (k' + l) + m' * (l' + k))) := congrArg (λ x => _ + (_ + (_ * _ + _ * x))) (Natural.add_commutative _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * k' + n' * l + m' * (l' + k))) := congrArg (λ x => _ + (_ + (x + _))) (Natural.left_distributive _ _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * k' + n' * l + (m' * l' + m' * k))) := congrArg (λ x => _ + (_ + (_ + _ + x))) (Natural.left_distributive _ _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * k' + (n' * l + (m' * l' + m' * k)))) := congrArg (λ x => (_ + (_ + x))) (Natural.add_associative _ _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * k' + ((n' * l + m' * l') + m' * k))) := congrArg (λ x => (_ + (_ + (_ + x)))) (Natural.add_associative _ _ _).symm
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * k' + ((m' * l' + n' * l) + m' * k))) := congrArg (λ x => (_ + (_ + (_ + (x + _))))) (Natural.add_commutative _ _).symm
    _ = (n * l + m * k) + ((n * k + m * l) + (n' * k' + (m' * l' + (n' * l + m' * k)))) := congrArg (λ x => (_ + (_ + (_ + x)))) (Natural.add_associative _ _ _)
    _ = (n * l + m * k) + ((n * k + m * l) + ((n' * k' + m' * l') + (n' * l + m' * k))) := congrArg (λ x => (_ + (_ + x))) (Natural.add_associative _ _ _).symm
    _ = ((n * l + m * k) + (n * k + m * l)) + ((n' * k' + m' * l') + (n' * l + m' * k)) := (Natural.add_associative _ _ _).symm
    _ = ((n * k + m * l) + (n * l + m * k)) + ((n' * k' + m' * l') + (n' * l + m' * k)) := congrArg (. + _) (Natural.add_commutative _ _)
    _ = (n * k + m * l) + ((n * l + m * k) + ((n' * k' + m' * l') + (n' * l + m' * k))) := Natural.add_associative _ _ _
    _ = (n * k + m * l) + (((n * l + m * k) + (n' * k' + m' * l')) + (n' * l + m' * k)) := congrArg (_ + .) (Natural.add_associative _ _ _).symm
    _ = (n * k + m * l) + (((n' * k' + m' * l') + (n * l + m * k)) + (n' * l + m' * k)) := congrArg (λ x => _ + (x + _)) (Natural.add_commutative _ _)
    _ = (n * k + m * l) + ((n' * l + m' * k) + ((n' * k' + m' * l') + (n * l + m * k))) := congrArg (_ + .) (Natural.add_commutative _ _)
    _ = ((n * k + m * l) + (n' * l + m' * k)) + ((n' * k' + m' * l') + (n * l + m * k)) := (Natural.add_associative _ _ _).symm
    _ = ((n' * k + m' * l) + (n * l + m * k)) + ((n' * k' + m' * l') + (n * l + m * k)) := congrArg (. + _) h₃
    _ = ((n * l + m * k) + (n' * k + m' * l)) + ((n' * k' + m' * l') + (n * l + m * k)) := congrArg (. + _) (Natural.add_commutative _ _)
  exact Natural.add_left_cancel h₄
  
instance : Mul Integer where mul := multiply

@[simp] theorem multiply_definition : multiply a b = a * b := rfl
  
theorem multiply_commutative : ∀ (a b : ℤ), a * b = b * a := by
  apply Quotient.ind₂
  intro (n, m) (k, l)
  apply Quotient.sound
  show (n * k + m * l) + (k * m + l * n) = (k * n + l * m) + (n * l + m * k)
  calc
    (n * k + m * l) + (k * m + l * n) = (k * n + m * l) + (k * m + l * n) := congrArg (λ x => (x + _) + _) (Natural.multiply_commutative n k)
    _ = (k * n + l * m) + (k * m + l * n) := congrArg (λ x => (_ + x) + _) (Natural.multiply_commutative m l)
    _ = (k * n + l * m) + (l * n + k * m) := congrArg (_ + .) (Natural.add_commutative (k * m) (l * n))
    _ = (k * n + l * m) + (n * l + k * m) := congrArg (λ x => _ + (x + _)) (Natural.multiply_commutative l n)
    _ = (k * n + l * m) + (n * l + m * k) := congrArg (λ x => _ + (_ + x)) (Natural.multiply_commutative k m)
    
theorem multiply_associative : ∀ (a b c : ℤ), (a * b) * c = a * (b * c) := by
  intro a b c
  let i := Quotient.mk instanceSetoidIntegerEquivalent
  suffices ∀ (a b c : ℕ × ℕ), multiply (multiply (i a) (i b)) (i c) = multiply (i a) (multiply (i b) (i c))
  from Quotient.inductionOn₃ a b c this
  intro (n, m) (k, l) (p, q)
  apply Quotient.sound
  show ((n*k + m*l)*p + (n*l + m*k)*q) + (n*(k*q + l*p) + m*(k*p + l*q)) = (n*(k*p + l*q) + m*(k*q + l*p)) + ((n*k + m*l)*q + (n*l + m*k)*p)
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
  calc
    (n * 1 + m * 0) + m = (n + m * 0) + m := congrArg (λ x => (x + _) + _) (Natural.multiply_one n)
    _ = (n + 0) + m := congrArg (λ x => (_ + x) + _) (Natural.multiply_zero m)
    _ = (n + n * 0) + m := congrArg (λ x => (_ + x) + _) (Natural.multiply_zero n).symm
    _ = n + (n * 0 + m) := Natural.add_associative n (n * 0) m
    _ = n + (n * 0 + m * 1) := congrArg (λ x => (_ + (_ + x))) (Natural.multiply_one m).symm

theorem left_distributive : ∀ (a b c : ℤ), a * (b + c) = a * b + a * c := by
  intro a b c
  let i := Quotient.mk instanceSetoidIntegerEquivalent
  suffices ∀ (a b c : ℕ × ℕ), multiply (i a) (add (i b) (i c)) = (multiply (i a) (i b)) + (multiply (i a) (i c))
  from Quotient.inductionOn₃ a b c this
  intro (n, m) (k, l) (p, q)
  apply Quotient.sound
  show (n*(k + p) + m*(l + q)) + ((n*l + m*k) + (n*q + m*p)) = ((n*k + m*l) + (n*p + m*q)) + (n*(l + q) + m*(k + p))
  calc
    (n*(k + p) + m*(l + q)) + ((n*l + m*k) + (n*q + m*p))
      = ((n*k + n*p) + m*(l + q)) + ((n*l + m*k) + (n*q + m*p)) := congrArg (λ x => (x + _) + _) (Natural.left_distributive _ _ _)
    _ = ((n*k + n*p) + (m*l + m*q)) + ((n*l + m*k) + (n*q + m*p)) := congrArg (λ x => (_ + x) + _) (Natural.left_distributive _ _ _)
    _ = (n*k + (n*p + (m*l + m*q))) + ((n*l + m*k) + (n*q + m*p)) := congrArg (. + _) (Natural.add_associative _ _ _)
    _ = (n*k + ((n*p + m*l) + m*q)) + ((n*l + m*k) + (n*q + m*p)) := congrArg (λ x => (_ + x) + _) (Natural.add_associative _ _ _).symm
    _ = (n*k + ((m*l + n*p) + m*q)) + ((n*l + m*k) + (n*q + m*p)) := congrArg (λ x => (_ + (x + _)) + _) (Natural.add_commutative _ _)
    _ = (n*k + (m*l + (n*p + m*q))) + ((n*l + m*k) + (n*q + m*p)) := congrArg (λ x => (_ + x) + _) (Natural.add_associative _ _ _)
    _ = ((n*k + m*l) + (n*p + m*q)) + ((n*l + m*k) + (n*q + m*p)) := congrArg (. + _) (Natural.add_associative _ _ _).symm
    _ = ((n*k + m*l) + (n*p + m*q)) + (n*l + (m*k + (n*q + m*p))) := congrArg (_ + .) (Natural.add_associative _ _ _)
    _ = ((n*k + m*l) + (n*p + m*q)) + (n*l + ((m*k + n*q) + m*p)) := congrArg (λ x => _ + (_ + x)) (Natural.add_associative _ _ _).symm
    _ = ((n*k + m*l) + (n*p + m*q)) + (n*l + ((n*q + m*k) + m*p)) := congrArg (λ x => (_ + _) + (_ + (x + _))) (Natural.add_commutative _ _)
    _ = ((n*k + m*l) + (n*p + m*q)) + (n*l + (n*q + (m*k + m*p))) := congrArg (λ x => _ + (_ + x)) (Natural.add_associative _ _ _)
    _ = ((n*k + m*l) + (n*p + m*q)) + ((n*l + n*q) + (m*k + m*p)) := congrArg (_ + .) (Natural.add_associative _ _ _).symm
    _ = ((n*k + m*l) + (n*p + m*q)) + (n*(l + q) + (m*k + m*p)) := congrArg (λ x => _ + (x + _)) (Natural.left_distributive _ _ _).symm
    _ = ((n*k + m*l) + (n*p + m*q)) + (n*(l + q) + m*(k + p)) := congrArg (λ x => _ + (_ + x)) (Natural.left_distributive _ _ _).symm
  
theorem right_distributive : ∀ (a b c : ℤ), (a + b) * c = a * c + b * c := by
  intro a b c
  calc
    (a + b) * c = c * (a + b) := multiply_commutative (a + b) c
    _ = c * a + c * b := left_distributive c a b
    _ = a * c + c * b := congrArg (. + _) (multiply_commutative c a)
    _ = a * c + b * c := congrArg (_ + .) (multiply_commutative c b)

instance : CommutativeRing Integer where
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
  
theorem add_inverse_left (a : ℤ) : -a + a = 0 := by
  rw [add_commutative, add_inverse]
  
theorem add_left_cancel {a b c : ℤ} (h : a + b = a + c) : b = c := by
  have : -a + (a + b) = -a + (a + c) := by rw [h]
  simp [← add_associative, add_inverse_left, zero_add] at this
  exact this
  
theorem add_right_cancel {a b c : ℤ} (h : a + c = b + c) : a = b := by
  rewrite [add_commutative a c, add_commutative b c] at h
  exact add_left_cancel h

@[simp]
def subtract (a b : ℤ) : ℤ := a + (-b)

instance : Sub Integer where sub := subtract

@[simp]
theorem subtract_definition (a b : ℤ) : a + (-b) = a - b := rfl

theorem subtract_self (a : ℤ) : a - a = 0 := add_inverse a

theorem negate_equal_of_add_equal_zero {a b : ℤ} (h : a + b = 0) : a = -b := by
  rw [← add_zero a, ← add_inverse (b), ← add_associative, h, zero_add]
    
theorem subtract_equal_zero_of_equal {a b : ℤ} (h : a = b) : a - b = 0 := by
  rw [← h, subtract_self]

theorem equal_of_subtract_equal_zero {a b : ℤ} (h : a - b = 0) : a = b := by
  rw [← add_zero a, ← add_inverse b, add_commutative b, ← add_associative, subtract_definition, h, zero_add]

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
  
-- Looked at hints, attempted a lifting proof and that's probably way overkill
theorem multiply_left_cancel {a b c : ℤ} (h_equivalent :  a * b = a * c) (h_not_equal_zero : a ≠ 0) : b = c := by
  have := calc
    0 = a*c - a*c := (add_inverse (a*c)).symm
    _ = a*c - a*b := congrArg (_ - .) h_equivalent.symm
    _ = a*c + -(a*b) := rfl
    _ = a*c + a*(-b) := congrArg (_ + .) (negate_multiply_equal_multiply_negate a b)
    _ = a*(c - b) := (left_distributive _ _ _).symm
  have : a = 0 ∨ c - b = 0 := equal_zero_of_multiply_equal_zero this.symm
  have : c - b = 0 := Or.resolve_left this h_not_equal_zero
  show b = c
  exact (equal_of_subtract_equal_zero this).symm

theorem multiply_right_cancel {a b c : ℤ} (h_equivalent : a * c = b * c) (h_not_equal_zero : c ≠ 0) : a = b := by
  have := calc
    c * a = a * c := multiply_commutative _ _
    _ = b * c := h_equivalent
    _ = c * b := multiply_commutative _ _
  exact multiply_left_cancel this h_not_equal_zero
  
-- TODO: Is it possible to remove this and decide a ≥ 0?
-- 0 + ↑n = a
-- (n, 0) ≈ (p, q)
-- ∃ n, q + n = p
-- q ≤ p
--
-- Yes, we can remove this concept entirely and jump straight to deciding a ≤ b by first proving that a ≤ b ↔ 0 ≤ b - a and then lowering 0 ≤ b - a to natural number less equal
--
-- We should keep this in and write about it
/-
def NonNegative : ℤ → Prop :=
  let nonNegative' := λ ((n, m) : ℕ × ℕ) => n ≥ m
  Quotient.lift nonNegative' <| by
  intro (n, m) (k, l) (h : n + l = k + m)
  apply propext
  apply Iff.intro
  . exact Natural.right_greater_equal_of_add_left_less_equal ((Natural.add_commutative _ _).trans h.symm)
  . exact Natural.right_greater_equal_of_add_left_less_equal ((Natural.add_commutative _ _).trans h)
-/
  
instance decideNonNegative (a : ℤ) : Decidable (NonNegative a) :=
  Quotient.recOnSubsingleton a λ ((n, m) : ℕ × ℕ) => Natural.decideLessEqual m n

def ofNatural (n : ℕ) : ℤ := ⟦(n, 0)⟧

instance : Coe Natural Integer := ⟨ofNatural⟩

theorem ofNatural_add (n m : ℕ) : ofNatural (n + m) = ofNatural n + ofNatural m := rfl

theorem ofNatural_multiply (n m : ℕ) : ofNatural (n * m) = ofNatural n * ofNatural m := by
  unfold ofNatural
  apply Quotient.sound
  show (n * m) + (n * 0 + 0 * m) = (n * m + 0 * 0) + 0
  simp [Natural.add_zero, Natural.zero_add, Natural.multiply_zero, Natural.zero_multiply]

theorem ofNatural_injective : Function.Injective ofNatural := by
  intro a b h
  calc
    a = a + 0 := (Natural.add_zero _).symm
    _ = b + 0 := Quotient.exact h
    _ = b := Natural.add_zero _

theorem ofNatural_nonnegative : ∀ n : ℕ, NonNegative (ofNatural n) := 
  Natural.zero_less_equal
  
theorem equal_ofNatural_of_nonnegative : ∀ {a : ℤ}, NonNegative a → ∃ n : ℕ, ↑n = a := by
  apply Quotient.ind
  intro (n, m) ⟨a, (ha : m + a = n)⟩
  apply Exists.intro a
  apply Quotient.sound
  show a + m = n + 0
  rw [Natural.add_commutative, Natural.add_zero, ha]

def LessEqual (a b : ℤ) : Prop := ∃ (n : ℕ), a + ↑n = b

instance : LE Integer where
  le := LessEqual
  
@[simp] theorem less_equal_definition : (LessEqual a b) = (a ≤ b) := rfl 

-- Curse you proof irrelevance!
-- Next step needed in calc proof is `Nat.add_sub_assoc`, but that requires a proof that k ≤ m
-- def positiveToNatural (a : ℤ) (h : a ≥ 0) : ℕ :=
  -- let positiveToNatural' := λ ((n, m) : ℕ × ℕ) => n - m
  -- Quotient.recOnSubsingleton a positiveToNatural' <| by
  --Quotient.liftOn a positiveToNatural' <| by
  --intro (n, m) (k, l) (h_equivalent : n + l = k + m)
  --show n - m = k - l
  --calc
    --n - m = ((n + l) - l) - m := congrArg (. - _) (Natural.add_subtract_self_right _ _).symm
    --_ = ((k + m) - l) - m := congrArg (λ x => (x - l) - m) h_equivalent
    --_ = (k + (m - l)) - m := sorry
    --_ = k - l := sorry

theorem LessEqual.reflexive : Relation.Reflexive LessEqual :=
  λ _ => Exists.intro 0 (add_zero _)

theorem LessEqual.antisymmetric : Relation.AntiSymmetric LessEqual := by
  intro a b ⟨n, hn⟩ ⟨m, hm⟩
  have := calc
    b + ↑(m + n) = b + (↑m + ↑n) := congrArg (_ + .) (ofNatural_add _ _)
    _ = (b + ↑m) + ↑n := (add_associative _ _ _).symm
    _ = a + ↑n := congrArg (. + _) hm
    _ = b := hn
    _ = b + 0 := (add_zero _).symm
  have : m = 0 ∧ n = 0 := 
    Natural.equal_zero_of_add_equal_zero (ofNatural_injective (add_left_cancel this))
  calc
    a = a + 0 := (add_zero _).symm
    _ = a + ↑n := congrArg (λ x => a + ↑x) this.right.symm
    _ = b := hn

theorem LessEqual.transitive : Relation.Transitive LessEqual := by
  intro a b c ⟨n, (h₁ : a + ↑n = b)⟩ ⟨m, (h₂ : b + ↑m = c)⟩
  apply Exists.intro ↑(n + m)
  calc
    a + ↑(n + m) = a + (↑n + ↑m) := congrArg (_ + .) (ofNatural_add _ _)
    _ = (a + ↑n) + ↑m := (add_associative _ _ _).symm
    _ = b + ↑m := congrArg (. + _) h₁
    _ = c := h₂
  
theorem greater_equal_zero_of_nonnegative : ∀ a : ℤ, NonNegative a → a ≥ 0 := by
  apply Quotient.ind
  intro (n, m) h_nonnegative
  exact equal_ofNatural_of_nonnegative h_nonnegative
  
theorem nonnegative_of_greater_equal_zero : ∀ a : ℤ, a ≥ 0 → NonNegative a := by
  apply Quotient.ind
  intro (n, m) h_greater_equal
  let ⟨a, (h_exists : 0 + ofNatural a = ⟦(n, m)⟧)⟩ := h_greater_equal
  -- TODO: Need to give the full type hint (i.e without nice ⟦(n, m)⟧ syntax) for this to work, how to change?
  have : ofNatural a = Quotient.mk instanceSetoidIntegerEquivalent (n, m) := ((zero_add _).symm.trans h_exists)
  exact this ▸ ofNatural_nonnegative a

theorem less_equal_of_subtract_greater_equal_zero {a b : ℤ} : b - a ≥ 0 → a ≤ b := by
  intro ⟨n, (h : 0 + ↑n = b - a)⟩
  apply Exists.intro n
  calc
    a + ↑n = ↑n + a := add_commutative _ _
    _ = 0 + (↑n + a) := (zero_add _).symm
    _ = (0 + ↑n) + a := (add_associative _ _ _).symm
    _ = (b - a) + a := congrArg (. + _) h
    _ = b + (-a + a) := add_associative _ _ _
    _ = b + (a + -a) := congrArg (_ + .) (add_commutative _ _)
    _ = b + 0 := congrArg (_ + .) (add_inverse _)
    _ = b := add_zero _

theorem subtract_greater_equal_zero_of_less_equal {a b : ℤ} : a ≤ b → b - a ≥ 0 := by
  intro ⟨n, (h : a + ↑n = b)⟩
  apply Exists.intro n
  calc
    0 + ↑n = (a + -a) + ↑n := congrArg (. + _) (add_inverse _).symm
    _ = (-a + a) + ↑n := congrArg (. + _) (add_commutative _ _)
    _ = -a + (a + ↑n) := add_associative _ _ _
    _ = -a + b := congrArg (_ + .) h
    _ = b - a := add_commutative _ _
    
instance decideLessEqual (a b : ℤ) : Decidable (a ≤ b) :=
  if h : NonNegative (b - a) then 
    isTrue ((less_equal_of_subtract_greater_equal_zero ∘ greater_equal_zero_of_nonnegative (b - a)) h)
  else 
    isFalse (mt (nonnegative_of_greater_equal_zero _ ∘ subtract_greater_equal_zero_of_less_equal) h)

instance decideNonNegative' (a : ℤ) : Decidable (0 ≤ a) :=
  have integer_nonnegative_of_positive_greater_equal_negative : ∀ {n m : ℕ}, n ≥ m → (0 : ℤ) ≤ ⟦(n, m)⟧ := by
  { intro n m ⟨a, (ha : m + a = n)⟩
    apply Exists.intro a
    apply Quotient.sound
    show (0 + a) + m = n + 0
    simp [Natural.add_zero, Natural.add_commutative, ha] }
  have positive_greater_equal_negative_of_integer_nonnegative : ∀ {n m : ℕ}, (0 : ℤ) ≤ ⟦(n, m)⟧ → n ≥ m := by
  { intro n m ⟨a, (ha : (0 : ℤ) + ↑a = ⟦(n, m)⟧)⟩
    have : (0 + a) + m = n + (0 + 0) := Quotient.exact ha
    simp [Natural.zero_add, Natural.add_commutative] at this
    exact (Exists.intro a this) }
  Quotient.recOnSubsingleton a 
  λ ((n, m) : ℕ × ℕ) =>
  if h : n ≥ m then
    isTrue (integer_nonnegative_of_positive_greater_equal_negative h)
  else
    isFalse (mt positive_greater_equal_negative_of_integer_nonnegative h)
    
instance decideLessEqual' (a b : ℤ) : Decidable (a ≤ b) :=
  if h : 0 ≤ b - a then
    isTrue (less_equal_of_subtract_greater_equal_zero h)
  else
    isFalse (mt subtract_greater_equal_zero_of_less_equal h)

theorem LessEqual.strongly_connected : Relation.StronglyConnected LessEqual :=
  have helper {n m k l : ℕ} : n + l ≤ k + m → LessEqual ⟦(n, m)⟧ ⟦(k, l)⟧ := by
  { intro ⟨a, (ha : (n + l) + a = k + m)⟩
    apply Exists.intro a
    apply Quotient.sound
    simp
    show (n + a) + l = k + m
    rw [Natural.add_right_commutative, ha]
  }
  Quotient.ind₂ λ (p, q) (s, t) =>
  Or.implies helper helper (Natural.LessEqual.strongly_connected (p + t) (s + q))
  
instance instanceTotalOrder : TotalOrder Integer where
  less_equal_reflexive := LessEqual.reflexive
  less_equal_antisymmetric := LessEqual.antisymmetric
  less_equal_transitive := LessEqual.transitive
  less_equal_strongly_connected := LessEqual.strongly_connected
  decidableEqual := decideEqual
  decidableLessEqual := decideLessEqual

def LessThan := instanceTotalOrder.less_than

/-
theorem less_than_of_subtract_positive {a b : ℤ} : 0 < b - a → a < b := by
  intro h
  have := less_than_equivalent_less_equal_not_less_equal.mp h
  apply less_than_equivalent_less_equal_not_less_equal.mpr
  apply And.intro
  . exact less_equal_of_subtract_greater_equal_zero this.left
  . intro g
    sorry

theorem subtract_positive_of_less_than {a b : ℤ} : a < b → 0 < b - a := by
  intro ⟨h_less_equal, (h_not_equal : a ≠ b)⟩
  apply And.intro
  . exact subtract_nonnegative_of_less_equal h_less_equal
  . intro h_equal
    have := (equal_of_subtract_equal_zero h_equal.symm).symm
    exact absurd this h_not_equal
-/

theorem add_left_less_equal (a b c : ℤ) (h : b ≤ c) : a + b ≤ a + c := by
  let ⟨n, hn⟩ := h
  apply Exists.intro n
  calc
    (a + b) + ↑n = a + (b + ↑n) := add_associative _ _ _
    _ = a + c := congrArg (_ + .) hn

theorem add_right_less_equal (a b c : ℤ) (h : a ≤ b) : a + c ≤ b + c := by
  rw [add_commutative a c, add_commutative b c]
  exact add_left_less_equal c a b h

/-
theorem add_left_less_than (a b c : ℤ) (h : b < c) : a + b < a + c := by
  let ⟨h_less_equal, h_not_equal⟩ := h
  apply And.intro
  . exact add_left_less_equal a b c h_less_equal
  . intro h_equal
    exact absurd (add_left_cancel h_equal) h_not_equal

theorem add_right_less_than (a b c : ℤ) (h : a < b) : a + c < b + c := by
  rw [add_commutative a c, add_commutative b c]
  exact add_left_less_than c a b h
-/

theorem multiply_less_equal_of_nonnegative_left {a b c : ℤ} (h_less_equal : b ≤ c) (h_positive : a ≥ 0) : a * b ≤ a * c := by
  let ⟨n, hn⟩ := h_less_equal
  let ⟨m, hm⟩ := h_positive
  apply Exists.intro ↑(m * n)
  calc
    a * b + ↑(m * n) = a * b + (↑m * ↑n) := congrArg (_ + .) (ofNatural_multiply _ _)
    _ = a * b + a * ↑n := congrArg (λ x => _ + x * _) ((zero_add _).symm.trans hm)
    _ = a * (b + ↑n) := (left_distributive _ _ _).symm
    _ = a * c := congrArg (_ * .) hn

theorem multiply_less_equal_of_nonnegative_right {a b c : ℤ} (h_less_equal : a ≤ b) (h_positive : c ≥ 0) : a * c ≤ b * c := by
  rw [multiply_commutative a c, multiply_commutative b c]
  exact multiply_less_equal_of_nonnegative_left h_less_equal h_positive

/-
theorem multiply_less_than_of_positive_left (a b c : ℤ) : b < c → a > 0 → a * b < a * c := sorry

theorem multiply_less_than_of_positive_right (a b c : ℤ) : a < b → c > 0 → a * c < b * c := sorry
-/

theorem negate_less_equal (a b : ℤ) (h_less_than : a ≤ b) : -b ≤ -a := by
  have := subtract_greater_equal_zero_of_less_equal h_less_than
  calc
    -b = -b + 0 := (add_zero _).symm
    _ ≤ -b + (b - a) := add_left_less_equal _ _ _ this
    _ = (-b + b) - a := (add_associative _ _ _).symm
    _ = 0 - a := congrArg (. - _) (add_inverse_left _)
    _ = -a := zero_add _

/-
theorem negate_less_than (a b : ℤ) : a < b → -b < -a := sorry
-/
