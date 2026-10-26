import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
A consequence of the already proposed source-scale interface: the first port
is forced positive by the positive literal source registers. This is a
standalone kernel, not a reimplementation of the source-row decoder.
-/
namespace FreshSimplifications

/-- One positive register and two natural-coordinate nonnegativity facts
force the port guard, positivity of the input coordinate, and q >= 2. -/
theorem port_pos_of_scale_rows {J beta L N : ℤ}
    (hJ : 0 ≤ J) (hL : 0 < L) (hN : 0 ≤ N)
    (hLrow : L = (1 + J * beta)^2 - 1)
    (hNrow : N = (1 + J * beta) * (1 + L)) :
    0 < J ∧ 0 < beta ∧ 2 ≤ 1 + J * beta := by
  have hq : 0 ≤ 1 + J * beta :=
    (mul_nonneg_iff_of_pos_right (by omega : 0 < 1 + L)).mp (hNrow ▸ hN)
  have hq2 : 2 ≤ 1 + J * beta := by nlinarith
  have hprod : 0 < J * beta := by omega
  rcases mul_pos_iff.mp hprod with hpos | hneg
  · exact ⟨hpos.1, hpos.2, hq2⟩
  · omega

/-- No positivity of N or J is assumed; both follow from the scale rows. -/
theorem eight_le_scale_of_rows {J beta L N : ℤ}
    (hJ : 0 ≤ J) (hL : 0 < L) (hN : 0 ≤ N)
    (hLrow : L = (1 + J * beta)^2 - 1)
    (hNrow : N = (1 + J * beta) * (1 + L)) : 8 ≤ N := by
  have hq2 := (port_pos_of_scale_rows hJ hL hN hLrow hNrow).2.2
  have hL3 : 3 ≤ L := by nlinarith
  calc
    8 = (2 : ℤ) * 4 := rfl
    _ ≤ (1 + J * beta) * (1 + L) :=
      mul_le_mul hq2 (by omega) (by omega) (by omega)
    _ = N := hNrow.symm

#print axioms port_pos_of_scale_rows
#print axioms eight_le_scale_of_rows
end FreshSimplifications
