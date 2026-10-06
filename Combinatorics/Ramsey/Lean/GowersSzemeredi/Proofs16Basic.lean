import GowersSzemeredi.Section16

/-!
# Basic proofs for Gowers's Section 16

This module proves the downward-closure property of multiple multilinearity:
the same box decomposition and multiaffine graphs that cover a relation also
cover every subrelation.
-/

set_option autoImplicit false

noncomputable section

open scoped ZMod

namespace LeanProofs.GowersSzemeredi

/-- Multiple multilinearity is inherited by subrelations. -/
theorem multiplyLinear_downward_closed_holds : multiplyLinear_downward_closed := by
  intro N k _ gamma r Gamma Gamma' hsubset hGamma theta htheta hthetaOne P hP
  obtain ⟨M, q, H, Q, mu, hHP, hHcard, hpartition, hproper, hq, hwidth, hmu, hcover⟩ :=
    hGamma theta htheta hthetaOne P hP
  refine ⟨M, q, H, Q, mu, hHP, hHcard, hpartition, hproper, hq, hwidth, hmu, ?_⟩
  intro j x hxQ hxH y hxy
  exact hcover j x hxQ hxH y (hsubset hxy)

end LeanProofs.GowersSzemeredi
