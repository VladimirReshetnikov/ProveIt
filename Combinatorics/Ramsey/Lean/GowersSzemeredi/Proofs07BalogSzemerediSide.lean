import GowersSzemeredi.Proofs07BalogSzemeredi

/-! Declarations of `Proofs07BalogSzemeredi` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

/-- **Gowers, Proposition 7.3.** Large additive energy contains a large
subset with quantitatively small difference set. -/
theorem proposition_7_3_holds : proposition_7_3 := by
  intro n A c hc henergy
  exact proposition_7_3_group_holds A c hc henergy

end LeanProofs.GowersSzemeredi
