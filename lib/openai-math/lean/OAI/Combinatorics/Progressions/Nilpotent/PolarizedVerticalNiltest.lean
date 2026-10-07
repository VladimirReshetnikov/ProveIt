import OAI.Combinatorics.Progressions.Estimates.ComplexPolarization
import OAI.Combinatorics.Progressions.Estimates.SourceUnitCover

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct NNReal

variable {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p)

noncomputable def coordinateCombination (i j : I) (c : ℂ) (x : D.Space) : ℂ :=
  V.observable i x + c * V.observable j x

theorem coordinateCombination_norm (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1) (x : D.Space) :
    ‖V.coordinateCombination i j c x‖ ≤ 2 := by
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hmul := mul_le_mul hc (V.norm j x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  linarith [V.norm i x]

theorem coordinateCombination_lipschitz (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    letI := D.metricSpace
    LipschitzWith (2 * V.lipBound) (V.coordinateCombination i j c) := by
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hi := (V.lipschitz i).dist_le_mul x y
  have hj := (V.lipschitz j).dist_le_mul x y
  rw [dist_eq_norm] at hi hj ⊢
  have he : V.coordinateCombination i j c x - V.coordinateCombination i j c y =
      (V.observable i x - V.observable i y) + c * (V.observable j x - V.observable j y) := by
    unfold coordinateCombination
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hm := mul_le_mul_of_nonneg_right hc (norm_nonneg (V.observable j x - V.observable j y))
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  nlinarith

theorem coordinateCombination_vertical (i j : I) (c : ℂ) (z : D.RealGroup) (hz : z ∈ T)
    (x : D.Space) : V.coordinateCombination i j c (z • x) =
      CircleFourier.character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle) *
        V.coordinateCombination i j c x := by
  unfold coordinateCombination
  rw [V.vertical i z hz, V.vertical j z hz]
  ring

noncomputable def combinationNiltest {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    D.Niltest w where
  orbit := g
  observable := V.coordinateCombination i j c
  normBound := 2
  lipBound := 2 * V.lipBound
  norm_le := V.coordinateCombination_norm i j c hc
  lipschitz := V.coordinateCombination_lipschitz i j c hc

theorem combinationNiltest_complexity {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    (V.combinationNiltest g i j c hc).ComplexityLE (p + 5) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (2 : ℝ) + ((2 * V.lipBound : ℝ≥0) : ℝ)) ≤ p + 5
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  calc
    _ ≤ 6 * Real.exp p := by nlinarith [V.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 5 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (5 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
