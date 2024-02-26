namespace Function

def Injective (f : α → β) := ∀ {a b}, f a = f b → a = b

def Surjective (f : α → β) := ∀ b, ∃ a, f a = b

def Bijective (f : α → β) := Injective f ∧ Surjective f

end Function
