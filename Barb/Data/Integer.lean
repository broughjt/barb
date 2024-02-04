import Barb.Algebra
import Barb.Quotient
import Barb.Syntax
import Barb.Data.Natural

open Natural (zero successor)

def integerEquivalent : (ℕ × ℕ) → (ℕ × ℕ) → Prop
  | (n, m), (n', m') => n + m' = n' + m

theorem integerEquivalent.reflexive (x : ℕ × ℕ) : integerEquivalent x x := rfl
  
theorem integerEquivalent.symmetric : ∀ {x y}, (integerEquivalent x y) → (integerEquivalent y x) := Eq.symm

theorem integerEquivalent.transitive : ∀ {x y z}, 
  integerEquivalent x y → integerEquivalent y z → integerEquivalent x z
  | (a, b), (c, d), (e, f), h1, h2 =>
    have h3 : a + d = c + b := h1
    have h4 : c + f = e + d := h2
    have h5 := calc
      (a + d) + (c + f) = (c + b) + (c + f) := congrArg (. + (c + f)) h3
      _                 = (c + b) + (e + d) := congrArg ((c + b) + .) h4
    have h6 := calc
      (a + d) + (c + f) = (d + a) + (c + f) := congrArg (. + (c + f)) (Natural.add_commutative a d)
      _ = d + (a + (c + f)) := Natural.add_associative d a (c + f)
      _ = d + ((a + c) + f) := congrArg (d + .) (Natural.add_associative a c f).symm
      _ = d + ((c + a) + f) := congrArg (λ x => d + (x + f)) (Natural.add_commutative a c)
      _ = d + (c + (a + f)) := congrArg (d + .) (Natural.add_associative c a f)
      _ = (d + c) + (a + f) := (Natural.add_associative d c (a + f)).symm
      _ = (c + d) + (a + f) := congrArg (. + (a + f)) (Natural.add_commutative d c)
    have h7 := calc
      (c + b) + (e + d) = (c + b) + (d + e) := congrArg ((c + b) + .) (Natural.add_commutative e d)
      _ = ((c + b) + d) + e := (Natural.add_associative (c + b) d e).symm
      _ = (c + (b + d)) + e := congrArg (. + e) (Natural.add_associative c b d)
      _ = (c + (d + b)) + e := congrArg (λ x => (c + x) + e) (Natural.add_commutative b d)
      _ = ((c + d) + b) + e := congrArg (. + e) (Natural.add_associative c d b).symm
      _ = (c + d) + (b + e) := Natural.add_associative (c + d) b e
      _ = (c + d) + (e + b) := congrArg ((c + d) + .) (Natural.add_commutative b e)
    have : (c + d) + (a + f) = (c + d) + (e + b) := (h6.symm.trans h5).trans h7
    Natural.add_left_cancel this

theorem integerEquivalence.is_equivalence : Equivalence integerEquivalent :=
  { refl := integerEquivalent.reflexive, symm := integerEquivalent.symmetric, trans := integerEquivalent.transitive }

instance instanceHasEquivIntegerEquivalent : HasEquiv (ℕ × ℕ) where
  Equiv := integerEquivalent
  
instance instanceSetoidIntegerEquivalent : Setoid (ℕ × ℕ) where
  r := integerEquivalent
  iseqv := integerEquivalence.is_equivalence

def Integer := Quotient instanceSetoidIntegerEquivalent

namespace Integer

notation "ℤ" => Integer

-- instance : Coe Natural Integer := ⟨Integer.ofNatural⟩

instance : OfNat Integer n where
  ofNat := Quotient.mk' (Natural.natToNatural n, 0)

instance Zero : Integer := Quotient.mk' (0, 0)

instance One : Integer := Quotient.mk' (1, 0)

def negate : ℤ → ℤ := 
  let negate' := λ ((n, m) : ℕ × ℕ) => (m, n)
  Quotient.map negate' <| by
  intro (n, m) (n', m') (h_equivalent : n + m' = n' + m)
  show m + n' = m' + n
  simp [Natural.add_commutative, h_equivalent]

instance : Neg Integer where
  neg := negate

def add : ℤ → ℤ → ℤ :=
  let add' := λ ((n, m) : ℕ × ℕ) ((k, l) : ℕ × ℕ) => (n + k, m + l)
  Quotient.map₂ add' <| by
  intro (n, m) (n', m') (h1 : n + m' = n' + m)
  intro (k, l) (k', l') (h2 : k + l' = k' + l)
  show (n + k) + (m' + l') = (n' + k') + (m + l)
  calc
    (n + k) + (m' + l') = ((n + k) + m') + l' := (Natural.add_associative (n + k) m' l').symm
    _ = (n + (k + m')) + l' := congrArg (. + l') (Natural.add_associative n k m')
    _ = (n + (m' + k)) + l' := congrArg (λ x => (n + x) + l') (Natural.add_commutative k m')
    _ = ((n + m') + k) + l' := congrArg (. + l') (Natural.add_associative n m' k).symm
    _ = ((n' + m) + k) + l' := congrArg (λ x => (x + k) + l') h1
    _ = (n' + m) + (k + l') := Natural.add_associative (n' + m) k l'
    _ = (n' + m) + (k' + l) := congrArg ((n' + m) + .) h2
    _ = ((n' + m) + k') + l := (Natural.add_associative (n' + m) k' l).symm
    _ = (n' + (m + k')) + l := congrArg (. + l) (Natural.add_associative n' m k')
    _ = (n' + (k' + m)) + l := congrArg (λ x => (n' + x) + l) (Natural.add_commutative m k')
    _ = ((n' + k') + m) + l := congrArg (. + l) (Natural.add_associative n' k' m).symm
    _ = (n' + k') + (m + l) := Natural.add_associative (n' + k') m l

instance : Add Integer where add := add

theorem add_commutative : ∀ (a b : ℤ), a + b = b + a := by
  apply Quotient.ind₂
  intro (n, m) (k, l)
  apply Quotient.sound
  show (n + k) + (l + m) = (k + n) + (m + l)
  simp [Natural.add_commutative]

theorem add_associative : ∀ (a b c : ℤ), (a + b) + c = a + (b + c) := by
  intro a b c
  -- TODO: ind₃
  let i := Quotient.mk instanceSetoidIntegerEquivalent
  suffices ∀ (a b c : ℕ × ℕ), add (add (i a) (i b)) (i c) = add (i a) (add (i b) (i c)) from Quotient.inductionOn₃ a b c this
  intro (n, m) (k, l) (o, p)
  apply Quotient.sound
  show ((n + k) + o) + (m + (l + p)) = (n + (k + o)) + ((m + l) + p)
  simp [Natural.add_associative]

theorem add_identity : ∀ (a : ℤ), a + 0 = a := by
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

theorem multiply_identity : ∀ (a : ℤ), a * 1 = a := by
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
  add_identity := add_identity
  add_inverse := add_inverse

  multiply_commutative := multiply_commutative
  multiply_associative := multiply_associative
  multiply_identity := multiply_identity

  left_distributive := left_distributive
  right_distributive := right_distributive

def subtract (a b : ℤ) : ℤ := a + (-b)

instance : Sub Integer where sub := subtract

theorem equal_zero_of_multiply_equal_zero : ∀ {a b : ℤ}, a * b = 0 → a = 0 ∨ b = 0 := by
  apply Quotient.ind₂
  intro (n, m) (k, l) h
  apply Quotient.sound

  
theorem multiply_equal_zero_of_equal_zero : ∀ {a b : ℤ}, a = 0 ∨ b = 0 → a * b = 0 := by
  sorry
  
theorem multiply_left_cancel : ∀ {a b c : ℤ}, a * b = a * c → a ≠ 0 → b = c := by
  sorry
  
theorem multiply_right_cancel : ∀ {a b c : ℤ}, a * c = b * c → c ≠ 0 → a = b := by
  sorry

-- TODO: Need to either define HAdd ℤ ℕ, or look into casting. There's cons to both but I think casting might be the way
-- def lessThan (a b : ℤ) : Prop := ∃ (n : ℕ), a + (cast n) = b
