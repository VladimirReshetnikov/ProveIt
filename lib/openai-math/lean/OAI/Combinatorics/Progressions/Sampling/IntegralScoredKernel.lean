import OAI.Combinatorics.Progressions.Geometry.NativeChartPartition
import OAI.Combinatorics.Progressions.Nilpotent.IntegralCentralNiltest

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_scored_native_chart (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      letI := D.metricSpace
      ∃ (r : ℝ≥0) (z : D.RealGroup) (phi : OpenPartialHomeomorph (Fin d → ℝ) D.Space),
        0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ i, |(D.basis.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
        (∀ v, phi v = QuotientGroup.mk
          (z * (NilpotentLieBCHGroup.basisHomeomorph (D.basis.baseChange ℝ)).symm v)) ∧
        phi.source = {v | ∀ i, |v i| < (r : ℝ)} ∧
        ∃ U : D.Niltest w, U.orbit = T.orbit ∧ U.UnitIntervalValued ∧
          U.ComplexityLE ((p + 2) ^ C) ∧ HasCompactSupport U.observable ∧
          tsupport U.observable ⊆ phi.target ∧
          (Real.exp (-((p + 2) ^ C)) ≤ 𝔼 x, a x * (U.eval (u x)).re) ∧
          tsupport U.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4) ∧
          ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
            LipschitzOnWith K phi phi.source := by
  obtain ⟨A, hA, hpartition⟩ := exists_native_chart_partition s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Polynomial.X + (Polynomial.X + 2) ^ A + 4)
  refine ⟨C, hC, ?_⟩
  intro σ X L _ _ _ d _ _ _ _ D w T a u p hp hT hpositive hscore
  let := D.metricSpace
  obtain ⟨r, hr, hr1, hri, n, hn, hnb, centers, phi, hcenters, hphi, hsource,
    P, hP, f, hfrange, hfsum, hfsupport, hfLip, hfInner, K, hK, hForward⟩ := hpartition D hp hT.1
  let q : ℝ := (p + 2) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by omega)
  have hb : p + q + 4 ≤ (p + 2) ^ C := by
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  let point : X → D.Space := fun x => QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w (u x) T.orbit)
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, hj⟩ := exists_weighted_partition_score
    (fun x => a x * (T.eval (u x)).re) (fun j x => f j (point x))
    (fun x => hfsum (point x)) hscore
  let U := T.positiveLocalization hpositive (f j) (hfrange j) P (hfLip j)
  have hU : U.ComplexityLE ((p + 2) ^ C) :=
    (T.positiveLocalization_complexity hpositive (f j) (hfrange j) P (hfLip j)
      hq (hT.mono hpq) hP).mono (by linarith)
  have hsupp : tsupport U.observable ⊆ tsupport (f j) :=
    T.positiveLocalization_support hpositive (f j) (hfrange j) P (hfLip j)
  refine ⟨r, centers j, phi j, hr, hr1, hri.trans (Real.exp_le_exp.mpr hqC),
    fun i => (hcenters j i).trans (Real.exp_le_exp.mpr hqC), hphi j, hsource j,
    U, rfl, T.positiveLocalization_unit_interval hpositive (f j) (hfrange j) P (hfLip j),
    hU, (hfsupport j).1.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans (hfsupport j).2, ?_, hsupp.trans (hfInner j), K,
    hK.trans (Real.exp_le_exp.mpr hqC), hForward j⟩
  have hnj : (0 : ℝ) < n := by exact_mod_cast hn
  have hscoreU : Real.exp (-p) / n ≤ 𝔼 x, a x * (U.eval (u x)).re := by
    simpa only [Fintype.card_fin, U, Niltest.positiveLocalization_eval_re,
      point, mul_assoc] using hj
  calc
    _ ≤ Real.exp (-p - q) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-p) / Real.exp q := Real.exp_sub _ _
    _ ≤ Real.exp (-p) / n := div_le_div_of_nonneg_left (Real.exp_nonneg _) hnj hnb
    _ ≤ _ := hscoreU

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal BigOperators

theorem exists_integral_scored_chart (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      ∃ (E : RationalFilteredNilmanifold L s (finrank ℚ L)) (omega : Fin (finrank ℚ L) → ℕ),
        E.filtration = D.filtration ∧ Monotone omega ∧ IsCentralLieBasis E.basis ∧
        (∀ i, 1 ≤ omega i ∧ omega i ≤ s) ∧
        (∀ k, E.filtration.layer k = Submodule.span ℚ (E.basis '' {i | k ≤ omega i})) ∧
        4 ≤ E.grid ∧ E.lattice ≤ D.lattice ∧ (E.lattice.subgroupOf D.lattice).FiniteIndex ∧
        bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid ∧
        (∀ g ∈ E.lattice, ∃! z : Fin (finrank ℚ L) → ℤ,
          integralOrderedBasisProduct E.basis E.filtration.lowerCentralSeries_eq_bot E.grid z = g) ∧
        letI := E.metricSpace
        ∃ (r : ℝ≥0) (z : E.RealGroup)
          (phi : OpenPartialHomeomorph (Fin (finrank ℚ L) → ℝ) E.Space),
          0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
          (∀ i, |(E.basis.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
          (∀ v, phi v = QuotientGroup.mk
            (z * (NilpotentLieBCHGroup.basisHomeomorph (E.basis.baseChange ℝ)).symm v)) ∧
          phi.source = {v | ∀ i, |v i| < (r : ℝ)} ∧
          ∃ V : E.Niltest w, V.UnitIntervalValued ∧ V.ComplexityLE ((p + 2) ^ C) ∧
            HasCompactSupport V.observable ∧ tsupport V.observable ⊆ phi.target ∧
            (Real.exp (-((p + 2) ^ C)) ≤ 𝔼 x, a x * (V.eval (u x)).re) ∧
            tsupport V.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4) ∧
            ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
              LipschitzOnWith K phi phi.source := by
  obtain ⟨A, hA, hlift⟩ := exists_integral_central_niltest_lift s
  obtain ⟨B, hB, hchart⟩ := exists_scored_native_chart s
  let C := (A + 2) * B
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro σ X L _ _ _ d _ _ _ _ D w T a u p hp hT hpositive hscore
  obtain ⟨E, omega, hEF, hmono, hcentral, hweights, hlayers, hgrid, hsub, hfinite,
    hcoords, hordered, U, hUpositive, hU, heval⟩ := hlift D T hp hT hpositive
  let := E.metricSpace
  let q : ℝ := (p + 2) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by omega)
  have hscoreU : Real.exp (-q) ≤ 𝔼 x, a x * (U.eval (u x)).re := by
    simpa only [heval] using (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hscore
  obtain ⟨r, z, phi, hr, hr1, hri, hz, hphi, hsource, V, _, hVpositive, hV,
    hcompact, hsupport, hscoreV, hinner, K, hK, hForward⟩ := hchart E U a u hq hU hUpositive hscoreU
  have hb : (q + 2) ^ B ≤ (p + 2) ^ C := shifted_power_budget_le hp A B
  have hexp := Real.exp_le_exp.mpr hb
  exact ⟨E, omega, hEF, hmono, hcentral, hweights, hlayers, hgrid, hsub, hfinite,
    hcoords, hordered, r, z, phi, hr, hr1, hri.trans hexp,
    fun i => (hz i).trans hexp, hphi, hsource, V, hVpositive, hV.mono hb,
    hcompact, hsupport, (Real.exp_le_exp.mpr (neg_le_neg hb)).trans hscoreV,
    hinner, K, hK.trans hexp, hForward⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal BigOperators

theorem exists_integral_scored_kernel (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      ∃ (E : RationalFilteredNilmanifold L s (finrank ℚ L)) (omega : Fin (finrank ℚ L) → ℕ),
        E.filtration = D.filtration ∧ Monotone omega ∧ IsCentralLieBasis E.basis ∧
        (∀ i, 1 ≤ omega i ∧ omega i ≤ s) ∧
        (∀ k, E.filtration.layer k = Submodule.span ℚ (E.basis '' {i | k ≤ omega i})) ∧
        4 ≤ E.grid ∧ E.lattice ≤ D.lattice ∧ (E.lattice.subgroupOf D.lattice).FiniteIndex ∧
        bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid ∧
        (∀ g ∈ E.lattice, ∃! z : Fin (finrank ℚ L) → ℤ,
          integralOrderedBasisProduct E.basis E.filtration.lowerCentralSeries_eq_bot E.grid z = g) ∧
        letI := E.metricSpace
        ∃ (r : ℝ≥0) (z : E.RealGroup)
          (phi : OpenPartialHomeomorph (Fin (finrank ℚ L) → ℝ) E.Space),
          0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
          (∀ i, |(E.basis.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
          (∀ v, phi v = QuotientGroup.mk
            (z * (NilpotentLieBCHGroup.basisHomeomorph (E.basis.baseChange ℝ)).symm v)) ∧
          phi.source = {v | ∀ i, |v i| < (r : ℝ)} ∧
          ∃ V : E.Niltest w, V.UnitIntervalValued ∧ V.ComplexityLE ((p + 2) ^ C) ∧
            (Real.exp (-((p + 2) ^ C)) ≤ 𝔼 x, a x * (V.eval (u x)).re) ∧
            tsupport V.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4) ∧
            ∃ Phi : PatchKernel (finrank ℚ L),
              Real.log (2 + (Phi.lip : ℝ)) ≤ (p + 2) ^ C ∧
              (∀ v, Phi.value v = chartCoordinateKernel phi (fun x => (V.observable x).re)
                ((E.grid : ℝ) • v)) ∧
              ∀ x ∈ phi.target,
                Phi.value (fun i => phi.symm x i / E.grid) = (V.observable x).re := by
  obtain ⟨A, _, hchart⟩ := exists_integral_scored_chart s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (3 * (Polynomial.X + 2) ^ A + 6)
  refine ⟨C, hC, ?_⟩
  intro σ X L _ _ _ d _ _ _ _ D w T a u p hp hT hpositive hscore
  obtain ⟨E, omega, hEF, hmono, hcentral, hweights, hlayers, hgrid, hsub, hfinite,
    hcoords, hordered, r, z, phi, hr, hr1, hri, hz, hphi, hsource,
    V, hVpositive, hV, _, _, hscoreV, hinner, K, hK, hForward⟩ :=
    hchart D T a u hp hT hpositive hscore
  let := E.metricSpace
  let q : ℝ := (p + 2) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 3 * q + 6 ≤ (p + 2) ^ C := by
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  have hexp := Real.exp_le_exp.mpr hqC
  let Phi := V.chartKernel hVpositive phi K r hr hr1 hsource hinner hForward hgrid
  have hPhi : Real.log (2 + (Phi.lip : ℝ)) ≤ (p + 2) ^ C :=
    (V.chartKernel_log_bound hVpositive phi K r hr hr1 hsource hinner hForward hgrid
      hq hV hK hri).trans hb
  refine ⟨E, omega, hEF, hmono, hcentral, hweights, hlayers, hgrid, hsub, hfinite,
    hcoords, hordered, r, z, phi, hr, hr1, hri.trans hexp, fun i => (hz i).trans hexp,
    hphi, hsource, V, hVpositive, hV.mono hqC,
    (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hscoreV, hinner, Phi, hPhi, ?_, ?_⟩
  · exact V.chartKernel_value hVpositive phi K r hr hr1 hsource hinner hForward hgrid
  · intro x hx
    exact V.chartKernel_recover hVpositive phi K r hr hr1 hsource hinner hForward hgrid hx

end Erdos3.RationalFilteredNilmanifold

end

end OAI
