def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

-- Copied from mathlib4/Mathlib/Init/Logic.lean

open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

/-- Pretty-printing for `ExistsUnique`, following the same pattern as pretty printing
    for `Exists`. -/
@[app_unexpander ExistsUnique] def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident ↦ ∃! $xs:binderIdent*, $b) => `(∃! $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident ↦ $b)                      => `(∃! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) ↦ $b)               => `(∃! ($x:ident : $t), $b)
  | _                                               => throw ()

theorem ExistsUnique.introduction {p : α → Prop} (w : α)
  (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x := ⟨w, h₁, h₂⟩

theorem ExistsUnique.elimination {p : α → Prop} (b : Prop)
  (h₂ : ∃! x, p x) (h₁ : ∀ x, p x → (∀ y, p y → y = x) → b) : b :=
  Exists.elim h₂ (λ w hw => h₁ w hw.left hw.right)

-- theorem ExistsUnique.elimination
