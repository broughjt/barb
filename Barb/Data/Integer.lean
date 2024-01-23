import Barb.Data.Natural

open Natural (zero successor)

inductive Integer : Type where
  | ofNatural : Natural → Integer
  | negativeSuccessor : Natural → Integer

namespace Integer

open Integer (ofNatural negativeSuccessor)

notation "ℤ" => Integer

instance : Coe Natural Integer := ⟨Integer.ofNatural⟩

instance : OfNat Integer n where
  ofNat := Integer.ofNatural (Natural.natToNatural n)
  
def negativeOfNatural : ℕ → ℤ
  | 0 => 0
  | Natural.successor n => negativeSuccessor n

def negate (n : ℤ) : ℤ :=
  match n with
  | ofNatural n => negativeOfNatural n
  | negativeSuccessor n => successor n

@[default_instance mid]
instance : Neg Integer where
  neg := negate

def subtractNaturalToInteger (n m : ℕ) : ℤ :=
  match (m - n : ℕ) with
  | 0 => ofNatural (n - m)
  | successor k => negativeSuccessor k

def add : ℤ → ℤ → ℤ
  | ofNatural n, ofNatural m => ofNatural (n + m)
  | ofNatural n, negativeSuccessor m => subtractNaturalToInteger n (successor m)
  | negativeSuccessor n, ofNatural m => subtractNaturalToInteger m (successor n)
  | negativeSuccessor n, negativeSuccessor m => negativeSuccessor (successor (n + m))

instance : Add Integer where
  add := Integer.add

def subtract (a b : ℤ) : ℤ := a + (-b)

instance : Sub Integer where
  sub := Integer.subtract

def multiply : ℤ → ℤ → ℤ
  | ofNatural n, ofNatural m => ofNatural (n * m)
  | ofNatural n, negativeSuccessor m => negativeOfNatural (n * successor m)
  | negativeSuccessor n, ofNatural m => negativeOfNatural (successor n * m)
  | negativeSuccessor n, negativeSuccessor m => ofNatural (successor n * successor m)

instance : Mul Integer where
  mul := Integer.multiply
