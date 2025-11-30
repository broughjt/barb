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

universe u₁ u₂ v₁ v₂
variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}
variable (R : α → β → Prop) (S : γ → δ → Prop)

def LiftFunction (f : α → γ) (g : β → δ) : Prop :=
  ∀ {a b}, R a b → S (f a) (g b)

infixr:40 " ⇒ " => LiftFunction
