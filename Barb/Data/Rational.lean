import Barb.Data.Integer
import Barb.Logic

-- Oh nice, that is very helpful!
abbrev NonZeroInteger := {a : ℤ // a ≠ 0}

def RationalEquivalent : (ℤ × NonZeroInteger) → (ℤ × NonZeroInteger) → Prop
  | (a, ⟨b, _⟩), (a', ⟨b', _⟩) => a * b' = a' * b

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
    have cd_nonzero := Integer.multiply_not_equal_zero_of_not_equal_zero c_nonzero d_nonzero
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
  ofNat := ⟦(Integer.ofNatural (Natural.natToNatural n), ⟨1, by decide⟩)⟧
  
instance Zero : Rational := ⟦(0, ⟨1, by decide⟩)⟧

instance One : Rational := ⟦(1, ⟨1, by decide⟩)⟧

def add : ℚ → ℚ → ℚ :=
  let add' := λ 
  ((a, ⟨b, b_nonzero⟩) : ℤ × NonZeroInteger) 
  ((c, ⟨d, d_nonzero⟩) : ℤ × NonZeroInteger) => 
  let bd_nonzero := Integer.multiply_not_equal_zero_of_not_equal_zero b_nonzero d_nonzero
  (a*d + c*b, ⟨b*d, bd_nonzero⟩)
  Quotient.map₂ add' <| by
  intro (a, ⟨b, b_nonzero⟩) (a', ⟨b', b'_nonzero⟩) (h₁ : a * b' = a' * b)
  intro (c, ⟨d, d_nonzero⟩) (c', ⟨d', d'_nonzero⟩) (h₂ : c * d' = c' * d)
  show (a*d + c*b) * (b'*d') = (a'*d' + c'*b') * (b*d)
  rw [Integer.right_distributive, ← Integer.multiply_associative (a * d) b' d', Integer.multiply_associative a d b', Integer.multiply_commutative d b', ← Integer.multiply_associative a b' d, h₁, Integer.multiply_commutative b' d', ← Integer.multiply_associative (c * b) d' b', Integer.multiply_associative c b d', Integer.multiply_commutative b d', ← Integer.multiply_associative c d' b, h₂, Integer.multiply_associative (a' * b) d d', Integer.multiply_commutative d d', Integer.multiply_associative a' b (d' * d), ← Integer.multiply_associative b d' d, Integer.multiply_commutative b d', Integer.multiply_associative d' b d, ← Integer.multiply_associative a' d' (b * d), Integer.multiply_associative (c' * d) b b', Integer.multiply_commutative b b', ← Integer.multiply_associative (c' * d) b' b, Integer.multiply_associative c' d b', Integer.multiply_commutative d b', ← Integer.multiply_associative c' b' d, Integer.multiply_associative (c' * b') d b, Integer.multiply_commutative d b, ← Integer.right_distributive]
  
def multiply : ℚ → ℚ → ℚ :=
  let multiply' := λ
  ((a, ⟨b, b_nonzero⟩) : ℤ × NonZeroInteger) 
  ((c, ⟨d, d_nonzero⟩) : ℤ × NonZeroInteger) => 
  let bd_nonzero := Integer.multiply_not_equal_zero_of_not_equal_zero b_nonzero d_nonzero
  (a*c, ⟨b*d, bd_nonzero⟩)
  Quotient.map₂ multiply' <| by
  intro (a, ⟨b, b_nonzero⟩) (a', ⟨b', b'_nonzero⟩) (h₁ : a * b' = a' * b)
  intro (c, ⟨d, d_nonzero⟩) (c', ⟨d', d'_nonzero⟩) (h₂ : c * d' = c' * d)
  show (a*c) * (b'*d') = (a'*c') * (b*d)
  calc
    (a*c) * (b'*d') 
      = (a*b') * (c*d') := by simp [Integer.multiply_associative, Integer.multiply_commutative, Integer.multiply_left_commutative]
    _ = (a'*b) * (c*d') := congrArg (. * _) h₁
    _ = (a'*b) * (c'*d) := congrArg (_ * .) h₂
    _ = (a'*c') * (b*d) := by simp [Integer.multiply_associative, Integer.multiply_commutative, Integer.multiply_left_commutative]
  
def negate : ℚ → ℚ :=
  let negate' := λ ((a, ⟨b, b_nonzero⟩) : ℤ × NonZeroInteger) => (-a, ⟨b, b_nonzero⟩)
  Quotient.map negate' <| by
  intro (a, ⟨b, b_nonzero⟩) (a', ⟨b', b'_nonzero⟩) (h : a*b' = a'*b)
  show (-a)*b' = (-a')*b
  rw [← Integer.negate_multiply_equal_negate_multiply, h, Integer.negate_multiply_equal_negate_multiply]
  
abbrev NonZeroRational := {a : ℚ // a ≠ 0}

def prereciprocal (x : ℤ × NonZeroInteger) : Rational :=
  if h : x.1 = 0 then 0 else ⟦(x.2.1, ⟨x.1, h⟩)⟧
  
@[simp]
theorem prereciprocal_zero (x : ℤ × NonZeroInteger) (hx : x.1 = 0) : prereciprocal x = 0 := by
  simp [prereciprocal, hx]

@[simp]
theorem prereciprocal_not_equal_zero (x : ℤ × NonZeroInteger) (hx : x.1 ≠ 0) :
    prereciprocal x = ⟦(x.2.1, ⟨x.1, hx⟩)⟧ := by
  simp [prereciprocal, hx]

def reciprocal' : ℚ → ℚ :=
  Quotient.lift prereciprocal <| by
  intro ⟨a, b, hab⟩ ⟨c, d, hcd⟩ (h : a * d = c * b)
  cases Decidable.em (a = 0)
  <;> cases Decidable.em (b = 0)
  <;> simp_all [prereciprocal, prereciprocal_zero, prereciprocal_not_equal_zero]
  case inl.inr _ => 
    rw [Integer.zero_multiply] at h
    have := Or.resolve_right (Integer.equal_zero_of_multiply_equal_zero h.symm) hab
    simp [this]
  case inr.inr quux =>
    have foo := Integer.multiply_not_equal_zero_of_not_equal_zero quux hcd
    have bar : c * b ≠ 0 := λ hn => foo (hn.symm.trans h.symm).symm
    have qar := Integer.not_equal_zero_of_multiply_not_equal_zero bar
    simp [qar.left]
    apply Quotient.sound
    show b * c = d * a
    simp [h, Integer.multiply_commutative]

def reciprocal (a : ℚ) : a ≠ 0 → ℚ := λ _ => reciprocal' a

-- def reciprocal (a : ℚ) : a ≠ 0 → ℚ :=
--   -- Quotient.mk instanceSetoidRationalEquivalent (a, { val := b, property := b_nonzero }) ≠ 0 → ℚ : Type
--   let reciprocal' := 
--     λ (x : ℤ × NonZeroInteger) => 
--     λ (x_nonzero : Quotient.mk instanceSetoidRationalEquivalent x ≠ (0 : ℚ)) => 
--     have x1_nonzero : x.1 ≠ 0 := by
--     { intro hx1
--       have foo := calc
--         x.1 * 1 = x.1 := Integer.multiply_one _
--         _ = 0 := hx1
--         _ = 0 * x.2.val := (Integer.zero_multiply _).symm
--       exact x_nonzero (Quotient.sound foo)
--     }
--     Quotient.mk instanceSetoidRationalEquivalent (x.2.val, ({ val := x.1, property := x1_nonzero } : NonZeroInteger))
--   Quotient.recOn a reciprocal' <| by
  
  -- intro (a, ⟨b, b_nonzero⟩) (a', ⟨b', b'_nonzero⟩) (h : a * b' = a' * b)
  

    /-
    let a_nonzero : a ≠ 0 := by
    { intro ha
      let blue := ((a : ℤ), ({ val := (b : ℤ), property := (b_nonzero : b ≠ (0 : ℤ)) } : NonZeroInteger))
      let zero := ((0 : ℤ), ({ val := (1 : ℤ), property := (by decide : (1 : ℤ) ≠ (0 : ℤ)) } : NonZeroInteger))
      have foo := calc
        a * 1 = a := Integer.multiply_one _
        _ = 0 := ha
        _ = 0 * b := (Integer.zero_multiply _).symm
      have bar : RationalEquivalent blue zero := foo
      have quux : ⟦(a, ({ val := b, property := b_nonzero } : NonZeroInteger))⟧ = ⟦(0, ({ val := 1, property := by decide } : NonZeroInteger))⟧ := 
        Quotient.sound (cast RationalEquivalent.definition.symm bar)
      exact ab_nonzero quux }
    ⟦(b, ⟨a, a_nonzero⟩)⟧
    -/
-- def reciprocal (a : ℚ) (a_nonzero : a ≠ 0) : ℚ :=
  -- let reciprocal' := λ ((a, ⟨b, b_nonzero⟩) : ℤ × NonZeroInteger) => (λ (a_foo : a * 1 ≠ 0 * b) => (b, ⟨a, sorry⟩))
  -- let proof1 := sorry
  -- Quotient.recOn (Quotient.recOn a reciprocal' proof1)


end Rational
