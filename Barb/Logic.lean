def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

@[app_unexpander ExistsUnique] def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident ↦ ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident ↦ $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) ↦ $b)               => `(∃! ($x:ident : $t), $b)
  | _                                               => throw ()

theorem ExistsUnique.introduction {p : α → Prop} (a : α)
  (h₁ : p a) (h₂ : ∀ y, p y → y = a) : ∃! x, p x := ⟨a, h₁, h₂⟩

theorem ExistsUnique.elimination {p : α → Prop} (b : Prop)
  (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ (λ w hw => h₁ w hw.left hw.right)

theorem or_imply : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  ⟨λ h => ⟨h ∘ .inl, h ∘ .inr⟩, λ ⟨ha, hb⟩ => Or.rec ha hb⟩

-- theorem not_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_imply

theorem Or.symmetric : a ∨ b → b ∨ a
  | inl a => inr a
  | inr b => inl b

theorem Or.commutative {a b : Prop} : a ∨ b ↔ b ∨ a := ⟨Or.symmetric, Or.symmetric⟩

theorem Or.implies {a b c d : Prop} (f : a → c) (g : b → d) : a ∨ b → c ∨ d
  | inl a => Or.inl (f a)
  | inr b => Or.inr (g b)
  
theorem Or.implies_left {a b c : Prop} (f : a → b) : a ∨ c → b ∨ c
  | inl a => Or.inl (f a)
  | inr c => Or.inr c
  
theorem Or.implies_right {a b c : Prop} (f : b → c) : a ∨ b → a ∨ c
  | inl a => Or.inl a
  | inr b => Or.inr (f b)

-- theorem Or.resolve_left {a b : Prop} (h : a ∨ b) (not_a : ¬a) : b :=
  -- match h with
  -- | Or.inl ha => absurd ha not_a
  -- | Or.inr hb => hb

-- theorem Or.resolve_right {a b : Prop} (h : a ∨ b) (not_b : ¬b) : a :=
  -- match h with
  -- | Or.inl ha => ha
  -- | Or.inr hb => absurd hb not_b

namespace Relation

variable {α : Sort u} (r : α → α → Prop)

local infix:50 " ≺ " => r
local notation:50 a:50 " ⊀ " b:50 => ¬(a ≺ b)

def Reflexive := ∀ x, x ≺ x

def Symmetric := ∀ {x y}, x ≺ y → y ≺ x

def Transitive := ∀ {x y z}, x ≺ y → y ≺ z → x ≺ z

def Irreflexive := ∀ x, x ⊀ x

def AntiSymmetric := ∀ {x y}, x ≺ y → y ≺ x → x = y

def Asymmetric := ∀ {x y}, x ≺ y → y ⊀ x

def Connected := ∀ {x y}, x ≠ y → x ≺ y ∨ y ≺ x

def StronglyConnected := ∀ x y, x ≺ y ∨ y ≺ x

end Relation

namespace Relator

universe u₁ u₂ v₁ v₂
variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}
variable (R : α → β → Prop) (S : γ → δ → Prop)

def LiftFunction (f : α → γ) (g : β → δ) : Prop :=
  ∀ {a b}, R a b → S (f a) (g b)

infixr:40 " ⇒ " => LiftFunction

end Relator
