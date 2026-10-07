import Mathlib.GroupTheory.Coset.Defs
import OAI.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eq_one_of_subgroup_grid_of_small_coordinates (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Γ)
    (hsmall : ∀ i, |e.repr g.coord i| < 1 / (l : ℝ)) : g = 1 := by
  apply ext
  apply e.equivFun.injective
  simpa only [coord_one, map_zero] using
    eq_zero_of_mem_realDenominatorGrid_of_abs_lt hl (hgrid g hg) hsmall

variable [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem quotient_coordinate_injOn_of_radius
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hsep : bchBoxCoordinateBound s (Fintype.card ι) H 1 * (2 * r) < 1 / (l : ℝ))
    (z : NilpotentLieBCHGroup L s hnil) :
    Set.InjOn (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ))
      {v | ∀ i, |v i| ≤ r} := by
  intro x hx y hy hxy
  let u := (basisHomeomorph (hnil := hnil) e).symm x
  let v := (basisHomeomorph (hnil := hnil) e).symm y
  have hu : e.equivFun u.coord = x := (basisHomeomorph (hnil := hnil) e).apply_symm_apply x
  have hv : e.equivFun v.coord = y := (basisHomeomorph (hnil := hnil) e).apply_symm_apply y
  have hur (i) : |e.repr u.coord i| ≤ r := by simpa only [← hu, Basis.equivFun_apply] using hx i
  have hvr (i) : |e.repr v.coord i| ≤ r := by simpa only [← hv, Basis.equivFun_apply] using hy i
  have hmem : u⁻¹ * v ∈ Γ := by
    have h := QuotientGroup.eq.mp hxy
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h
  have hone : u⁻¹ * v = 1 := by
    apply eq_one_of_subgroup_grid_of_small_coordinates e Γ l hl hgrid _ hmem
    intro k
    have hbound := lieBCH_sub_coordinates_bound e c hstructure hc hnil (-u.coord) (-v.coord)
      (B := 1) (δ := 2 * r) le_rfl (by positivity)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using (hur i).trans hr1)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using (hvr i).trans hr1)
      (fun i => by
        simp only [map_neg, Finsupp.neg_apply, neg_sub_neg]
        exact (abs_sub _ _).trans (by linarith [hur i, hvr i])) k
    simpa only [coord_mul, coord_inv, neg_neg] using hbound.trans_lt hsep
  have huv : u = v := inv_mul_eq_one.mp hone
  exact hu.symm.trans ((congrArg (fun g => e.equivFun g.coord) huv).trans hv)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
