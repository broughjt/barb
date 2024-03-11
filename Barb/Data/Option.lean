/-
For now, this goes in here and this file exists. I have no patience for figuring out why the actual `Option.get` isn't in scope.
-/

namespace Option

@[inline] def get {α : Type u} : (o : Option α) → Option.isSome o → α
  | some x, _ => x   
  
@[simp] theorem get_some (x : α) (h : Option.isSome (some x)) : (some x).get h = x := rfl

end Option
