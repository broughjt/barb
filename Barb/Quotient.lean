namespace Relator
universe u₁ u₂ v₁ v₂

section

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}
variable (R : α → β → Prop) (S : γ → δ → Prop)

-- Above my pay grade as an undergraduate taking foundations of analysis, we will return to this at a future time.

/-- The binary relations `R : α → β → Prop` and `S : γ → δ → Prop` induce a binary
    relation on functions `LiftFun : (α → γ) → (β → δ) → Prop`. -/
def LiftFunction (f : α → γ) (g : β → δ) : Prop :=
  ∀ {a b}, R a b → S (f a) (g b)

/-- `(R ⇒ S) f g` means `LiftFunction R S f g`. -/
infixr:40 " ⇒ " => LiftFunction

end

end Relator

namespace Quot

-- notation:arg "⟦" a "⟧" => Quotient.mk _ a
variable {ra : α → α → Prop} {rb : β → β → Prop} {φ : Quot ra → Quot rb → Sort foo}
variable {γ : Sort bar} {r : α → α → Prop} {s : β → β → Prop}

@[elab_as_elim]
theorem induction_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r)
    (h : ∀ a, β (Quot.mk r a)) : β q :=
  Quot.ind h q

def map (f : α → β) (h : (ra ⇒ rb) f f) : Quot ra → Quot rb :=
  (Quot.lift λ x => (Quot.mk _ (f x))) λ x y (h₁ : ra x y) ↦ Quot.sound <| h h₁
  
def lift₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) (q₁ : Quot r) (q₂ : Quot s) : γ :=
  Quot.lift (fun a ↦ Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha ↦ funext fun q ↦ Quot.induction_on q fun b ↦ hs a₁ a₂ b ha) q₁ q₂

def map₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (q₁ : Quot r) (q₂ : Quot s) : Quot t :=
  Quot.lift₂ (fun a b ↦ Quot.mk t <| f a b) (fun a b₁ b₂ hb ↦ Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha ↦ Quot.sound (hs a₁ a₂ b ha)) q₁ q₂

end Quot

namespace Quotient

variable [sa : Setoid α] [sb : Setoid β]
variable {φ : Quotient sa → Quotient sb → Sort u}

def map (f : α → β) (h : ((· ≈ ·) ⇒ (· ≈ ·)) f f) : Quotient sa → Quotient sb :=
  Quot.map f h
  
end Quotient
