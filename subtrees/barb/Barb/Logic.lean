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

theorem And.associative {a b c : Prop} : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
  Iff.intro
    (λ ⟨⟨a, b⟩, c⟩ => ⟨a, ⟨b, c⟩⟩)
    (λ ⟨a, ⟨b, c⟩⟩ => ⟨⟨a, b⟩, c⟩)

theorem And.symmetric {a b : Prop} : a ∧ b → b ∧ a := λ ⟨a, b⟩ => ⟨b, a⟩

theorem And.commutative {a b : Prop} : a ∧ b ↔ b ∧ a :=
  Iff.intro And.symmetric And.symmetric

theorem or_imply : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
  ⟨λ h => ⟨h ∘ .inl, h ∘ .inr⟩, λ ⟨ha, hb⟩ => Or.rec ha hb⟩

theorem Or.symmetric : a ∨ b → b ∨ a
  | inl a => inr a
  | inr b => inl b

theorem Or.commutative {a b : Prop} : a ∨ b ↔ b ∨ a :=
  Iff.intro Or.symmetric Or.symmetric

theorem Or.implies {a b c d : Prop} (f : a → c) (g : b → d) : a ∨ b → c ∨ d
  | inl a => Or.inl (f a)
  | inr b => Or.inr (g b)
  
theorem Or.implies_left {a b c : Prop} (f : a → b) : a ∨ c → b ∨ c
  | inl a => Or.inl (f a)
  | inr c => Or.inr c
  
theorem Or.implies_right {a b c : Prop} (f : b → c) : a ∨ b → a ∨ c
  | inl a => Or.inl a
  | inr b => Or.inr (f b)
