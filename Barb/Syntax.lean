class Zero.{u} (α : Type u) where
  zero : α

instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

instance Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
  zero := 0

class One (α : Type u) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1
  
class Invert (α : Type u) where
  invert : α → α

class HeterogeneousInvert (α : Type u) (β : Type v) where
  heterogeneous_invert : α → β

postfix:max "⁻¹" => Invert.invert
postfix:max "⁻¹" => HeterogeneousInvert.heterogeneous_invert

class Infimum (α : Type u) where
  infimum : α → α → α

infixl:68 " ⊓ " => Infimum.infimum

class Supremum (α : Type u) where
  supremum : α → α → α

infixl:68 " ⊔ " => Supremum.supremum
