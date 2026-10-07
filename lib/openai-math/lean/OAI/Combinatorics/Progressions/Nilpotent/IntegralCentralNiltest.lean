import OAI.Combinatorics.Progressions.Estimates.CentralAdaptedRebase
import OAI.Combinatorics.Progressions.Estimates.LinearMapIntegralCover

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_integral_central_niltest_lift (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      ∃ (E : RationalFilteredNilmanifold L s (finrank ℚ L)) (omega : Fin (finrank ℚ L) → ℕ),
        E.filtration = D.filtration ∧ Monotone omega ∧ IsCentralLieBasis E.basis ∧
        (∀ i, 1 ≤ omega i ∧ omega i ≤ s) ∧
        (∀ k, E.filtration.layer k = Submodule.span ℚ (E.basis '' {i | k ≤ omega i})) ∧
        4 ≤ E.grid ∧ E.lattice ≤ D.lattice ∧ (E.lattice.subgroupOf D.lattice).FiniteIndex ∧
        bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid ∧
        (∀ g ∈ E.lattice, ∃! z : Fin (finrank ℚ L) → ℤ,
          integralOrderedBasisProduct E.basis E.filtration.lowerCentralSeries_eq_bot E.grid z = g) ∧
        ∃ U : E.Niltest w, U.UnitIntervalValued ∧ U.ComplexityLE ((p + 2) ^ C) ∧
          ∀ x : σ → ℤ, U.eval x = T.eval x := by
  obtain ⟨A, _, hrebase⟩ := exists_controlled_central_rebase
  obtain ⟨B, _, hcover⟩ := exists_controlled_integral_coordinates s
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ A + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D w T p hp hT hpositive
  obtain ⟨F, H, hH, hmono, hcentral, hweights, hpA, hF, htests⟩ := hrebase D hp hT.1
  let U₀ := F.rebaseNiltest H hH T
  have hU₀ : U₀.ComplexityLE ((p + 2) ^ A) := htests T hT
  let q₀ : ℝ := (p + 2) ^ A
  let q : ℝ := q₀ + 4
  let Hc := ⌈Real.exp q₀⌉₊
  have hq₀ : 0 ≤ q₀ := by dsimp [q₀]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq₀q : q₀ ≤ q := by dsimp [q]; linarith
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hlp : ((4 * F.grid : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ 4 * Real.exp q₀ := mul_le_mul_of_nonneg_left hF.2.1 (by norm_num)
      _ ≤ Real.exp 4 * Real.exp q₀ := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = Real.exp q := by rw [← Real.exp_add]; congr 1; dsimp [q]; ring
  have hHcp : (Hc : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hq₀).trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  have hdivgrid : F.grid ∣ 4 * F.grid := dvd_mul_left _ _
  have hinner : scaledIntegerGrid (4 * F.grid) ⊆ bchSubgroupCoordinates F.basis D.lattice :=
    (scaledIntegerGrid_subset_of_dvd hdivgrid).trans F.inner
  have houter : bchSubgroupCoordinates F.basis D.lattice ⊆ denominatorGrid (4 * F.grid) :=
    F.outer.trans (denominatorGrid_subset_of_dvd hdivgrid)
  obtain ⟨m, Λ, hm, hdiv, hmb, hΛ, hfinite, hcoords, hordered⟩ :=
    hcover F.basis hcentral D.filtration.lowerCentralSeries_eq_bot D.lattice
      (4 * F.grid) Hc q (Nat.mul_pos (by decide) F.grid_pos)
      (fun i j k => rationalHeightLE_ceil_exp (hF.2.2.1 i j k)) hinner houter hq
      (hF.1.trans hq₀q) hHcp hlp
  have hm4 : 4 ≤ m := by
    have hn := F.grid_pos
    have hle : 4 * F.grid ≤ m := Nat.le_of_dvd hm hdiv
    omega
  have hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates F.model.basis Λ := hcoords.symm.le
  have hout : bchSubgroupCoordinates F.model.basis Λ ⊆ denominatorGrid m := by
    change bchSubgroupCoordinates F.basis Λ ⊆ denominatorGrid m
    rw [hcoords]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid m m hx
  let E := F.model.withLattice Λ m hm hin hout
  let U : E.Niltest w := U₀.onSublattice Λ m hm hin hout hΛ
  have hcost : q + (q + B) ^ B ≤ (p + 2) ^ C := by
    simpa [Q, q, q₀, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (q + B) ^ B ≤ (p + 2) ^ C := (le_add_of_nonneg_left hq).trans hcost
  have hE : E.GeometryComplexityLE ((p + 2) ^ C) :=
    F.model.withLattice_geometry Λ m hm hin hout hF (hq₀q.trans hqC)
      (hmb.trans (Real.exp_le_exp.mpr hBC))
  refine ⟨E, F.weight, rfl, hmono, hcentral, hweights, F.layers, hm4, hΛ, hfinite,
    hcoords, hordered, U, ?_, ?_, ?_⟩
  · exact U₀.onSublattice_unit_interval Λ m hm hin hout hΛ hpositive
  · exact U₀.onSublattice_complexity Λ m hm hin hout hΛ (hU₀.mono (hq₀q.trans hqC)) hE
  · intro x
    rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
