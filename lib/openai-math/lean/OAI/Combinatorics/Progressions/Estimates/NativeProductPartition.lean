import OAI.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric
import OAI.Combinatorics.Progressions.Nilpotent.NativeNiltestPartition

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_product_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ : Type*} [Fintype ι] [DecidableEq ι]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (w : σ → ℕ) {p ρ : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ g : (pi D).filtration.realification.PolynomialOrbit w,
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : Fin n → (pi D).Niltest w,
            (∀ j, (A j).orbit = g) ∧
            (∀ j, (A j).UnitIntervalValued) ∧
            (∀ j, (A j).ComplexityLE ((p + C) ^ C)) ∧
            (∀ z, ∑ j, ((A j).observable z).re = 1) ∧
            (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
             ∀ j x y, 0 < ((A j).observable x).re → 0 < ((A j).observable y).re →
               ∀ i, dist (productProjection D i x) (productProjection D i y) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_native_niltest_partition s 1
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + 2) ^ 2 + (X + 4) ^ 4 + (X + 2) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro ι σ _ _ L _ _ _ _ _ _ _ _ _ _ d D w p ρ hp hι hD hρ hρinv g
  let t := p + (p + 2) ^ 2 + (p + 4) ^ 4 + (p + 2) ^ a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hgeom : (p + 2) ^ 2 ≤ t := by
    dsimp [t]
    linarith [show 0 ≤ (p + 4) ^ 4 from by positivity,
      show 0 ≤ (p + 2) ^ a from by positivity]
  let ε := ρ / Real.exp ((p + 4) ^ 4)
  have hε : 0 < ε := div_pos hρ (Real.exp_pos _)
  have hεinv : 1 / ε ≤ Real.exp ((t + 2) ^ 1) := by
    calc
      _ = Real.exp ((p + 4) ^ 4) * (1 / ρ) := by dsimp [ε]; field_simp
      _ ≤ Real.exp ((p + 4) ^ 4) * Real.exp ((p + 2) ^ a) :=
        mul_le_mul_of_nonneg_left hρinv (Real.exp_pos _).le
      _ = Real.exp ((p + 4) ^ 4 + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; simp only [pow_one]; nlinarith [sq_nonneg (p + 2)])
  obtain ⟨n, hn, hnb, A, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition (pi D) w ht ((pi_geometry D hp hι hD).mono (pi D) hgeom) hε hεinv g
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A, horbit, hunit,
    fun j => (hcomplexity j).mono hcost, hsum, ?_⟩
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  intro j x y hx hy i
  have hxy := hdiam j x y hx hy
  have hprod := (productSpaceEquiv_lipschitz D).dist_le_mul x y
  have hcoord := dist_le_pi_dist (productSpaceEquiv D x) (productSpaceEquiv D y) i
  change dist (productProjection D i x) (productProjection D i y) ≤
    dist (productSpaceEquiv D x) (productSpaceEquiv D y) at hcoord
  calc
    _ ≤ (productMetricBound d : ℝ) * dist x y := hcoord.trans hprod
    _ ≤ (productMetricBound d : ℝ) * ε :=
      mul_le_mul_of_nonneg_left hxy (productMetricBound d).coe_nonneg
    _ ≤ Real.exp ((p + 4) ^ 4) * ε :=
      mul_le_mul_of_nonneg_right (productMetricBound_le_exp d hp hι (fun i => (hD i).1)) hε.le
    _ = ρ := by dsimp [ε]; field_simp

end Erdos3.RationalFilteredNilmanifold

end

end OAI
