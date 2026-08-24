import GowersSzemeredi.Section16

/-!
# Gowers (2001), Section 16: downward closure

This module proves the elementary downward-closure observation for multiply-
linear relations.  It is separated from the main induction so later proofs can
reuse the result without importing any of its quantitative machinery.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

/-- A subrelation of a multiply-linear relation is multiply linear with the
same parameters. -/
theorem multiplyLinear_downward_closed_holds :
    multiplyLinear_downward_closed := by
  intro N k _ gamma r Gamma Gamma' hsub hGamma theta htheta P
  obtain ⟨M, q, H, Q, mu, hHP, hHcard, hpartition, hq, hwidth,
      hmultilinear, hcover⟩ := hGamma theta htheta P
  refine ⟨M, q, H, Q, mu, hHP, hHcard, hpartition, hq, hwidth,
    hmultilinear, ?_⟩
  intro j x hxQ hxH y hxy
  exact hcover j x hxQ hxH y (hsub hxy)

end LeanProofs.GowersSzemeredi
