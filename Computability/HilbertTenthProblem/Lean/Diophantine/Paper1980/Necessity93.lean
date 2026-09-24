import Diophantine.Paper1980.NecessityCode93b
import Diophantine.Paper1980.NecessityPell93

/-!
# Necessity: an accepting computation yields a positive solution (Section 7)

The coding witnesses of `NecessityCode93a/b` and the Pell witnesses of
`NecessityPell93` assemble into a positive solution of the 93-operation
system at the fixed index `(V, H, Tindex)` of the circuit.
-/

namespace Jones1980

namespace Iso

open Layout
open Diophantine Pell

/-- Necessity: if the circuit accepts `x > 0` then the system has a positive solution. -/
theorem necessity (C : Gates.Circuit) {x : ℕ} (hx : 0 < x) (hacc : C.Accepts x) :
    Solvable93 x (cV C) (cH C) (cT C) := by
  obtain ⟨X, hX, hR⟩ := hacc
  have hx1 : 1 ≤ x := hx
  obtain ⟨tt, htt0, hE45⟩ := E45W C x X
  obtain ⟨jq, hjq1, hjq⟩ := qW_pow C x X
  have hcentral := centralW C x X hx1 hX hR
  obtain ⟨a, c, d, f, h, i, j, k, o, s, w, γ, η, τ', φ, κ, μ, ρ, Δ, ζ, pa, pc, pd, pf, ph, pi, pj,
    pk, po, ps, pw, pγ, pη, pτ, pφ, pκ, pμ, pρ, pΔ, pζ, E9, E10a, E10b, E11, E12, E13, E14, E15,
    E16, E17, E18, E19, E20⟩ :=
    pell_witnesses (r := rW C x X) (n := nW C x X) (q := qW C x X) (B := BW C x X) (L := cL C)
      (Tindex := cT C) (jq := jq) (rW_ge_two C x X) (nW_eq C x X) hjq hjq1 (nW_le_rW C x X)
      (BW_ge_64 C x X) (BW_le_qW C x X) (cL_ge C) (three_cL_le_BW C x X) (qW_eq C x X)
      (by unfold cT; rfl) hcentral
  have hxb := x_lt_bW C x X
  have hqpos : 0 < qW C x X := by have := qW_ge C x X; omega
  have hnpos : 0 < nW C x X := by have := qW_ge C x X; have := nW_ge C x X; omega
  have hlampos : 0 < lamW C x X := by have := eW_lt_lamW C x X; omega
  have hBZ : (BW C x X : ℤ) = (cH C : ℤ) + bW C x X + 4 := by
    rw [← radix_eq C x X]; push_cast; ring
  refine ⟨a, bW C x X, c, d, eW C x X, f, gW C x X, h, i, j, k, lW C x X, nW C x X, o, qW C x X,
    rW C x X, s, tt, w, qW C x X - lW C x X - eW C x X, γ, η, cH C + bW C x X, lamW C x X, τ', φ,
    κ, μ, ρ, Δ, bW C x X - x, ζ, σW C x X, ΩW C x X,
    pa, by omega, pc, pd, eW_pos C x X, pf, gW_pos C x X, ph, pi, pj, pk, lW_pos C x X, hnpos,
    po, hqpos, by have := rW_ge_two C x X; omega, ps, htt0, pw, αW_pos C x X, pγ, pη, by omega,
    hlampos, pτ, pφ, pκ, pμ, pρ, pΔ, βW_pos C x X, pζ, σW_pos C x X, ΩW_pos C x X, ?_⟩
  refine ⟨E1W C x X, E1bW C x X, E2W C x X, rfl, ?_, nW_eq C x X, ?_, E9, E10a, E10b, E11, E12,
    E13, E14, E15, E16, E17, ?_, E19, E20, ESW C x X, EΩW C x X⟩
  · rw [θW_eq]; exact hE45
  · have := E7W C x X; push_cast at this ⊢; linear_combination this
  · rw [hBZ] at E18; push_cast at E18 ⊢; linear_combination E18

end Iso

end Jones1980
