import Barb.Logic

namespace Quot

section

variable {ra : α → α → Prop} {rb : β → β → Prop}
variable {γ : Sort v} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

notation:arg "⟦" a "⟧" => Quot.mk _ a

@[elab_as_elim]
theorem induction_on {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r)
    (h : ∀ a, β (Quot.mk r a)) : β q :=
  Quot.ind h q

def map (f : α → β) (h : (ra ⇒ rb) f f) : Quot ra → Quot rb :=
  Quot.lift (λ x => ⟦f x⟧) (λ x y (h₁ : ra x y) => Quot.sound <| h h₁)

def lift₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) : Quot r → Quot s → γ :=
  Quot.lift (λ a => Quot.lift (f a) (hr a))
    (λ a₁ a₂ ha => funext λ q => Quot.induction_on q λ b => hs a₁ a₂ b ha)

def liftOn₂ (p : Quot r) (q : Quot s) (f : α → β → γ)
    (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) : γ :=
  Quot.lift₂ f hr hs p q

def map₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) : Quot r → Quot s → Quot t :=
  Quot.lift₂ (λ a b => Quot.mk t <| f a b) (λ a b₁ b₂ hb => Quot.sound (hr a b₁ b₂ hb))
    (λ a₁ a₂ b ha => Quot.sound (hs a₁ a₂ b ha))

@[elab_as_elim]
def recOnSubsingleton₂ {φ : Quot r → Quot s → Sort w} [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)]
    (q₁ : Quot r) (q₂ : Quot s)
    (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ := 
  @Quot.recOnSubsingleton _ r
    (λ q => φ q q₂)
    (λ a => Quot.ind (β := λ b => Subsingleton (φ ⟦a⟧ b)) (h a) q₂) q₁
    (λ a => Quot.recOnSubsingleton q₂ (λ b => f a b))

theorem lift_construct (f : α → β) (h : ∀ a b, r a b → f a = f b) (a : α) :
    Quot.lift f h (Quot.mk r a) = f a :=
  rfl

instance lift.decidablePredicate (r : α → α → Prop) (p : α → Prop) (h : ∀ a b, r a b → p a = p b)
    [hp : DecidablePred p] :
    DecidablePred (Quot.lift p h) :=
  λ q => Quot.recOnSubsingleton (motive := λ _ => Decidable _) q hp
  
instance lift₂.decidablePredicate (r : α → α → Prop) (s : β → β → Prop) (p : α → β → Prop)
    (ha : ∀ a b₁ b₂, s b₁ b₂ → p a b₁ = p a b₂) (hb : ∀ a₁ a₂ b, r a₁ a₂ → p a₁ b = p a₂ b)
    [hp : ∀ a, DecidablePred (p a)] (q₁ : Quot r) :
    DecidablePred (Quot.lift₂ p ha hb q₁) :=
  λ q₂ => Quot.recOnSubsingleton₂ q₁ q₂ hp
  
instance (r : α → α → Prop) (q : Quot r) (p : α → Prop) (h : ∀ a b, r a b → p a = p b)
    [DecidablePred p] :
    Decidable (Quot.liftOn q p h) :=
  Quot.lift.decidablePredicate _ _ _ _
  
instance (r : α → α → Prop) (s : β → β → Prop) (q₁ : Quot r) (q₂ : Quot s) (p : α → β → Prop)
    (ha : ∀ a b₁ b₂, s b₁ b₂ → p a b₁ = p a b₂) (hb : ∀ a₁ a₂ b, r a₁ a₂ → p a₁ b = p a₂ b)
    [∀ a, DecidablePred (p a)] :
    Decidable (Quot.liftOn₂ q₁ q₂ p ha hb) :=
  Quot.lift₂.decidablePredicate _ _ _ _ _ _ _

end

end Quot

namespace Quotient

section

variable [sa : Setoid α] [sb : Setoid β] [sc : Setoid γ]

def map (f : α → β) (h : ((· ≈ ·) ⇒ (· ≈ ·)) f f) : Quotient sa → Quotient sb :=
  Quot.map f h

def map₂ (f : α → β → γ) (h : ((· ≈ ·) ⇒ (· ≈ ·) ⇒ (· ≈ ·)) f f) :
    Quotient sa → Quotient sb → Quotient sc :=
  Quotient.lift₂ (λ x y => ⟦(f x y)⟧) (λ _ _ _ _ h₁ h₂ => Quot.sound <| h h₁ h₂)
  
@[elab_as_elim]
def ind₃ {motive : Quotient sa → Quotient sb → Quotient sc → Prop}
  (h : (a : α) → (b : β) → (c : γ) → motive ⟦a⟧ ⟦b⟧ ⟦c⟧)
  (q₁ : Quotient sa)
  (q₂ : Quotient sb)
  (q₃ : Quotient sc)
  : motive q₁ q₂ q₃ := by
  induction q₁ using Quotient.ind
  induction q₂ using Quotient.ind
  induction q₃ using Quotient.ind
  apply h
  
@[simp]
theorem lift_construct (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.lift f h (Quotient.mk sa x) = f x := 
  rfl

@[simp]
theorem lift_construct_on (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.liftOn (Quotient.mk sa x) f h = f x :=
  rfl

@[simp]
theorem equivalent [r : Setoid α] {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ x ≈ y :=
  ⟨Quotient.exact, Quotient.sound⟩

instance lift.decidablePred (p : α → Prop) (h : ∀ a b, a ≈ b → p a = p b) [DecidablePred p] :
    DecidablePred (Quotient.lift p h) :=
  Quot.lift.decidablePredicate _ _ _

instance lift₂.decidablePred (p : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → p a₁ b₁ = p a₂ b₂)
    [hf : ∀ a, DecidablePred (p a)]
    (q₁ : Quotient sa) : DecidablePred (Quotient.lift₂ p h q₁) :=
  λ q₂ ↦ Quotient.recOnSubsingleton₂ q₁ q₂ hf

instance (q : Quotient sa) (p : α → Prop) (h : ∀ a b, a ≈ b → p a = p b) [DecidablePred p] :
    Decidable (Quotient.liftOn q p h) :=
  Quotient.lift.decidablePred _ _ _

instance (q₁ : Quotient sa) (q₂ : Quotient sb) (p : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → p a₁ b₁ = p a₂ b₂) [∀ a, DecidablePred (p a)] :
    Decidable (Quotient.liftOn₂ q₁ q₂ p h) :=
  Quotient.lift₂.decidablePred _ _ _ _

end

end Quotient
