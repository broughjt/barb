class Zero.{u} (α : Type u) where
  zero : α

instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

instance Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
  zero := 0

class One (α : Type u) where
  one : α
-- #align has_one One

-- @[to_additive existing Zero.toOfNat0]
instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1
-- @[to_additive existing Zero.ofOfNat0, to_additive_change_numeral 2]
instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1
