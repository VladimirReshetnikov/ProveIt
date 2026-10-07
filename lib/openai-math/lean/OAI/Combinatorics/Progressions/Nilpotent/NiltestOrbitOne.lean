import OAI.Combinatorics.Progressions.Fourier.BoundedFrequencyKernel

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def oneOnOrbit (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun _ => 1
  normBound := 1
  lipBound := 0
  norm_le _ := by simp
  lipschitz := by
    let := D.metricSpace
    exact LipschitzWith.const 1

theorem oneOnOrbit_orbit (T : D.Niltest w) : T.oneOnOrbit.orbit = T.orbit := rfl

theorem oneOnOrbit_eval (T : D.Niltest w) (x : σ → ℤ) : T.oneOnOrbit.eval x = 1 := rfl

theorem oneOnOrbit_complexity (T : D.Niltest w) {p : ℝ} (hp : 2 ≤ p)
    (hD : D.GeometryComplexityLE p) : T.oneOnOrbit.ComplexityLE p := by
  refine ⟨hD, ?_⟩
  change Real.log (2 + 1 + 0) ≤ p
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at h ⊢
  linarith

theorem oneOnOrbit_vertical (T : D.Niltest w) (z : D.RealGroup) (x : D.Space) :
    T.oneOnOrbit.observable (z • x) =
      CircleFourier.character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
        T.oneOnOrbit.observable x := by
  simp only [oneOnOrbit, realifyFunctional_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, mul_one]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
