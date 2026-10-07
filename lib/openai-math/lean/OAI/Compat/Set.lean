/-
Added for ProveIt (not an upstream file; distributed under Apache-2.0).
Compatibility name for predicate-set membership in Lean 4.32 / Mathlib v4.32.0.
This is a definitional equality, proved locally without copying upstream code.
-/
import Mathlib.Data.Set.Defs

set_option autoImplicit false

theorem Set.mem_ofPred_eq {α : Type*} {p : α → Prop} {a : α} :
    (a ∈ {x | p x}) = p a := rfl
