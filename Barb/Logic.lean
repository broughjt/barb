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

theorem not_or : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_imply
