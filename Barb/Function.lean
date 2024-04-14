namespace Function

def Injective (f : α → β) := ∀ {x y}, f x = f y → x = y

def Surjective (f : α → β) := ∀ y, ∃ x, f x = y

def Bijective (f : α → β) := Injective f ∧ Surjective f

-- "g is a left inverse to f," that is, (g ∘ f) = id
def LeftInverse (g : β → α) (f : α → β) := ∀ x : α, (g ∘ f) x = x

-- "g is a right inverse to f," that is, (f ∘ g) = id
def RightInverse (g : β → α) (f : α → β) := LeftInverse f g

-- TODO: Prove that ∃ LeftInverse → Injective
-- TODO: Prove that ∃ RightInverse → Surjective

def Involutive (f : α → α) := LeftInverse f f

@[inline]
def curry : (α × β → φ) → α → β → φ := λ f a b => f (a, b)

@[inline]
def uncurry : (α → β → φ) → α × β → φ := λ f ⟨a, b⟩ => f a b

variable {α : Type u₁} {β : Type u₂} {φ : Type u₃}

@[simp]
theorem curry_uncurry_left_inverse : LeftInverse (curry : (α × β → φ) → α → β → φ) (uncurry : (α → β → φ) → α × β → φ) :=
  λ _ => rfl

@[simp]
theorem uncurry_curry_left_inverse : LeftInverse (uncurry : (α → β → φ) → α × β → φ) (curry : (α × β → φ) → α → β → φ) :=
  λ _ => funext λ _ => rfl

end Function
