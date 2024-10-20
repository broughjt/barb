module Function.Core where

open import Level using (Level)

private
  variable
    a b c : Level
    A : Set a
    B : Set b

identity : A → A
identity x = x

constant : A → B → A
constant x = λ _ → x

infixr 9 _∘_
-- infixl 0 _|>_
-- infixr -1 _$_

_∘_ : ∀ {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

flip : ∀ {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) → (y : B) → C x y) → ((y : B) → (x : A) → C x y)
flip f = λ y x → f x y
