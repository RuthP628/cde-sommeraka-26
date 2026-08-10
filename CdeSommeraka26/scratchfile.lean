import Mathlib

#check ℕ
#check Prop
#check Type
#check Type 1
#check Type 2
#check Type*

example {P : Type} {Q : Type} : ((P → Q) × P) → Q :=
    fun x ↦ x.1 x.2
