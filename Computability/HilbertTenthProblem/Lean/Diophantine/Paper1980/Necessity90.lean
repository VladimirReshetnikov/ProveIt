import Diophantine.Paper1980.NecessityCode90b
import Diophantine.Paper1980.NecessityPell90

/-!
# Necessity: an accepting computation yields a positive solution of the
90-operation system

The coding witnesses of `NecessityCode90a/b` and the Pell witnesses of
`NecessityPell90` assemble into a positive solution of the 90-operation system
at the fixed index `(V, H, Tindex)` of the circuit.
-/

namespace Jones1980

namespace L90

open Layout (Row)
open Diophantine Pell

/-- Necessity: if the circuit accepts `x > 0` then the system has a positive solution. -/
theorem necessity (C : Gates.Circuit) {x : ℕ} (hx : 0 < x) (hacc : C.Accepts x) :
    Solvable90 x (cV C) (cH C) (cT C) := by
  obtain ⟨X, hX, hR⟩ := hacc
  have hx1 : 1 ≤ x := hx
  obtain ⟨tt, htt0, hE45⟩ := E45W C x X
  obtain ⟨jq, hjq1, hjq⟩ := qW_pow C x X
  have hcentral := centralW C x X hx1 hX hR
  obtain ⟨a, c, d, f, h, i, j, k, o, s, w, γ, η, τ', φ, κ, μ, ρ, Δ, ζ, y, pa, pc, pd, pf, ph, pi,
    pj, pk, po, ps, pw, pγ, pη, pτ, pφ, pκ, pμ, pρ, pΔ, pζ, py, E9, E10a, E10b, E11, E12, E13,
    E14, E15, E16, E17, E17b, E18, E19, E20⟩ :=
    pell_witnesses90 (r := rW C x X) (n := nW C x X) (q := qW C x X) (B := BW C x X) (L := cL C)
      (Tindex := cT C) (jq := jq) (rW_ge_two C x X) (rW_even C x X) (nW_eq C x X) hjq hjq1
      (nW_le_rW C x X) (BW_ge_64 C x X) (BW_le_qW C x X) (cL_ge C) (three_cL_le_BW C x X)
      (qW_eq C x X) (by unfold cT; rfl) hcentral
  have hxb := x_lt_bW C x X
  have hqpos : 0 < qW C x X := by have := qW_ge C x X; omega
  have hnpos : 0 < nW C x X := by have := qW_ge C x X; have := nW_ge C x X; omega
  have hlampos := lamW_pos C x X
  have hH64 : 64 ≤ cH C := by have := H0_ge_1024 C; have := cH_eq C; omega
  have hBZ : (BW C x X : ℤ) = (cH C : ℤ) + bW C x X + 2 := by
    rw [← radix_eq C x X]; push_cast; ring
  refine ⟨a, bW C x X, c, d, eW C x X, f, gW C x X, h, i, j, k, lW C x X, nW C x X, o, qW C x X,
    rW C x X, s, tt, w, qW C x X - lW C x X - σW C x X, γ, η, cH C + bW C x X, lamW C x X, τ', φ,
    κ, μ, ρ, Δ, bW C x X - x, ζ, σW C x X, y,
    pa, by omega, pc, pd, eW_pos C x X, pf, gW_pos C x X, ph, pi, pj, pk, lW_pos C x X, hnpos,
    po, hqpos, by have := rW_ge_two C x X; omega, ps, htt0, pw, αW_pos C x X, pγ, pη, by omega,
    hlampos, pτ, pφ, pκ, pμ, pρ, pΔ, βW_pos C x X, pζ, σW_pos C x X, py, ?_⟩
  refine ⟨E1W C x X, E1bW C x X, E2W C x X, rfl, ?_, nW_eq C x X, ?_, E9, E10a, E10b, E11, E12,
    E13, E14, E15, E16, E17, E17b, ?_, E19, E20, ESW C x X⟩
  · rw [θW_eq]; exact hE45
  · have := E7W C x X; push_cast at this ⊢; linear_combination this
  · rw [hBZ] at E18; push_cast at E18 ⊢; linear_combination E18

end L90

end Jones1980
