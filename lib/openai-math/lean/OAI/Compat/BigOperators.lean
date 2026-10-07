/-
Added for ProveIt (not an upstream file; distributed with this directory under
the same Apache-2.0 license). Backport of declarations that the upstream
library uses from its newer toolchain (Lean v4.34.1, Mathlib d13f23b7) but that
are absent from this repository's Lean 4.32.0 / Mathlib v4.32.0. Statements
are the upstream ones. Delete when the toolchain is upgraded.
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option autoImplicit false

namespace Finset

alias prod_le_prod₀ := prod_le_prod
alias prod_le_one₀ := prod_le_one
alias one_le_prod₀ := one_le_prod
alias prod_le_prod_of_subset_of_one_le₀ := prod_le_prod_of_subset_of_one_le
alias prod_le_prod_of_subset_of_le_one₀ := prod_le_prod_of_subset_of_le_one

end Finset
