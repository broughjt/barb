#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Identity.Syntax where

open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Universe
```

= Equational reasoning syntax <note:3a94206b-78b0-41ad-830a-7e176246c13a>
 
Some dedicated syntax for performing step-wise applications of the
#link("note://984d4510-34b9-492f-a792-95a19117193e")[concatenation operation on
paths], which lets you explicitly write the values of the endpoints.

```agda
infixr 2 step-＝
step-＝ : {i : Level} {A : Type i}
          (x : A) {y z : A} → y ＝ z → x ＝ y → x ＝ z
step-＝ _ p q = q ∙ p

syntax step-＝ x y p = x ＝[ p ] y

infix  3 _∎
_∎ : {i : Level} {A : Type i}
     (x : A) → x ＝ x
_ ∎ = reflexive
```
