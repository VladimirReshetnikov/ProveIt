/-
Added for ProveIt (not an upstream file; distributed with this directory under
the same Apache-2.0 license). Backport of declarations that the upstream
library uses from its newer toolchain (Lean v4.34.1, Mathlib d13f23b7) but that
are absent from this repository's Lean 4.32.0 / Mathlib v4.32.0. Statements
are the upstream ones. Delete when the toolchain is upgraded.
-/
import Mathlib.LinearAlgebra.TensorProduct.Defs

set_option autoImplicit false

namespace TensorProduct

open scoped TensorProduct

@[elab_as_elim]
protected theorem inductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive <| x ⊗ₜ[R] y)
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add

end TensorProduct
