import Trace74BoundaryRecurrenceCast

/-! UNCHECKED DRAFT. Exact finite inequalities for the arbitrary-port seed.
`decide` is intended as a kernel-checked computation; success and its resource
cost are not asserted. This file does not yet instantiate the graph theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Trace74BoundaryNaturalSeed
open Trace74BoundaryRecurrenceCast

def S : ℕ := 0x20000007800000d980000fdc0000d61a0008b2a800487b7801f105800b29dfa03693d380e539ab83418be40a4f90521c8d8fa84557ca9893ee7d
def X : ℕ := 2^31
def Y : ℕ := 8*S
def firstBase : ℕ := 2*(X*Y*Y-1)+1
def K : ℕ := 2*(xy 16 firstBase).2
def C : ℕ := (xy 31 (Y*(X+1))).2

/-- Explicit finite interval: this is only a proposed kernel computation. -/
theorem interval : K*Y < C ∧ C < K*Y+K := by
  decide

/-- The interval supplies the positive first-Pell slack coordinates. -/
theorem slacks :
    0 < C-K*Y ∧ 0 < K-(C-K*Y) ∧
    C = K*Y+(C-K*Y) ∧ K = (C-K*Y)+(K-(C-K*Y)) := by
  have h := interval
  omega

#print axioms Trace74BoundaryNaturalSeed.interval
#print axioms Trace74BoundaryNaturalSeed.slacks
end Trace74BoundaryNaturalSeed
