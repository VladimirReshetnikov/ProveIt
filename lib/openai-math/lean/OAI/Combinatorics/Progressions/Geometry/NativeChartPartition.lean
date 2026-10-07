import OAI.Combinatorics.Progressions.Nilpotent.RealifiedBCHSmoothPartition
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

theorem exists_native_chart_partition (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      letI := D.metricSpace
      ∃ r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        ∃ centers : Fin n → D.RealGroup,
        ∃ phi : Fin n → OpenPartialHomeomorph (Fin d → ℝ) D.Space,
          (∀ j i, |(D.basis.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
          (∀ j v, phi j v = QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (D.basis.baseChange ℝ)).symm v)) ∧
          (∀ j, (phi j).source = {v | ∀ i, |v i| < (r : ℝ)}) ∧
          ∃ P : ℝ≥0, (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
          ∃ f : Fin n → D.Space → ℝ,
            (∀ j x, 0 ≤ f j x ∧ f j x ≤ 1) ∧ (∀ x, ∑ j, f j x = 1) ∧
            (∀ j, HasCompactSupport (f j) ∧ tsupport (f j) ⊆ (phi j).target) ∧
            (∀ j, LipschitzWith P (f j)) ∧
            (∀ j, tsupport (f j) ⊆ phi j '' Metric.closedBall 0 (3 * (r : ℝ) / 4)) ∧
            ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
              ∀ j, LipschitzOnWith K (phi j) (phi j).source := by
  obtain ⟨A, _, hpartition⟩ := exists_realification_smooth_partition_exp_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + 1 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ D p hp hD
  let := D.metricSpace
  let H := ⌈Real.exp p⌉₊
  have hc (i j k) : RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  obtain ⟨r, hr, hr1, hri, n, hn, hnb, centers, phi, hcenters, hphi, hsource, _,
    P, hP, f, hfrange, hfsum, hfsupport, _, hfLip, hfInner, K, hK, hForward⟩ :=
    hpartition D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid H (p + 1)
      D.grid_pos D.inner_grid D.outer_grid hc (by linarith)
      (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp)
      (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hb : (p + 1 + A) ^ A ≤ (p + 2) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have heb := Real.exp_le_exp.mpr hb
  exact ⟨r, hr, hr1, hri.trans heb, n, hn, hnb.trans heb, centers, phi,
    fun j i => (hcenters j i).trans heb, hphi, hsource, P, hP.trans heb,
    f, hfrange, hfsum, hfsupport, hfLip, hfInner, K, hK.trans heb, hForward⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
