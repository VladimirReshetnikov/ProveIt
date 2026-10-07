import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_rational_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup, (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          (∃ r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ) ∧
          (∃ r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = γ * r) := by
  obtain ⟨a, _, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hclosure⟩ := exists_real_bch_rational_closure s
  let X : Polynomial ℕ := Polynomial.X
  let P := (2 * X + 1 + Polynomial.C a) ^ a + (2 * X + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD q hq hqp
  let t := 2 * p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := (ceil_exp_le_exp_add_one hp).trans
    (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by
    simpa only [Fintype.card_fin] using hD.1.trans hpt
  have hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hprod : ((q * D.grid : ℕ) : ℝ) ≤ Real.exp t := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hqp hD.2.1 (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨m, hm, hmb, _, hmul, _⟩ := hclosure D.basis H t
    D.filtration.lowerCentralSeries_eq_bot ht hd hH hc (q * D.grid)
    (Nat.mul_pos hq D.grid_pos) hprod
  have hsum : (t + a) ^ a + (t + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (t + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (t + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg ht (Nat.cast_nonneg a)) _)).trans hsum
  have hright (g : D.RealGroup) (hg : (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q) :
      ∃ r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
        ∃ γ ∈ D.realLattice, g = r * γ := by
    obtain ⟨r, hr, γ, hγ, heq⟩ := hrep D.basis D.filtration.lowerCentralSeries_eq_bot
      D.lattice D.grid H t D.grid_pos D.inner_grid hc ht hd hH
      (hD.2.1.trans (Real.exp_le_exp.mpr hpt)) g
    have hγgrid := realification_subgroup_grid D.basis D.lattice D.grid D.outer_grid
      γ⁻¹ (D.realLattice.inv_mem hγ)
    have hrgrid : (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m := by
      have h := hmul g γ⁻¹
        (realDenominatorGrid_subset_of_dvd hq (dvd_mul_right q D.grid) hg)
        (realDenominatorGrid_subset_of_dvd D.grid_pos (dvd_mul_left D.grid q) hγgrid)
      simpa only [heq, mul_inv_cancel_right] using h
    exact ⟨r, fun i => (hr i).trans (Real.exp_le_exp.mpr haC), hrgrid, γ, hγ, heq⟩
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hg
  refine ⟨hright g hg, ?_⟩
  have hginv : (D.basis.baseChange ℝ).equivFun g⁻¹.coord ∈ realDenominatorGrid q := by
    change (D.basis.baseChange ℝ).equivFun (-g.coord) ∈ _
    rw [map_neg]
    exact realDenominatorGrid_neg q hg
  obtain ⟨r, hr, hrgrid, γ, hγ, heq⟩ := hright g⁻¹ hginv
  refine ⟨r⁻¹, ?_, ?_, γ⁻¹, D.realLattice.inv_mem hγ, ?_⟩
  · intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hr i
  · change (D.basis.baseChange ℝ).equivFun (-r.coord) ∈ _
    rw [map_neg]
    exact realDenominatorGrid_neg m hrgrid
  · have h := congrArg (fun z : D.RealGroup => z⁻¹) heq
    simpa only [inv_inv, mul_inv_rev] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
