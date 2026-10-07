import OAI.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation

namespace OAI

section

namespace Erdos3

theorem normalizedMesh_scale_lower {delta scale inverseLog lengthLog : ℝ}
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hscale : 4 * Real.exp (inverseLog + lengthLog) ≤ scale) :
    Real.exp lengthLog ≤ delta * scale / 4 := by
  have hinv' := mul_le_mul_of_nonneg_left hinv hdelta.le
  rw [mul_inv_cancel₀ hdelta.ne'] at hinv'
  have hprod := mul_le_mul_of_nonneg_right hinv' (by positivity : 0 ≤ 4 * Real.exp lengthLog)
  have hsize := mul_le_mul_of_nonneg_left hscale hdelta.le
  rw [Real.exp_add] at hsize
  nlinarith

theorem normalizedMesh_scale_large {delta scale inverseLog lengthLog : ℝ}
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hlength : 0 ≤ lengthLog) (hscale : 4 * Real.exp (inverseLog + lengthLog) ≤ scale) :
    4 ≤ delta * scale := by
  have h := normalizedMesh_scale_lower hdelta hinv hscale
  have hone := Real.one_le_exp_iff.mpr hlength
  linarith

theorem normalizedBoxPartitions_exp_lengths {I : Type*}
    (N : I → ℕ) (scale : I → ℝ) (delta inverseLog lengthLog : ℝ)
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hscale : ∀ i, 4 * Real.exp (inverseLog + lengthLog) ≤ scale i)
    (hlarge : ∀ i, 4 ≤ delta * scale i) (hwhole : ∀ i, delta * scale i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N scale delta hlarge hwhole i).Label) :
    Real.exp lengthLog ≤ ((normalizedBoxPartitions N scale delta hlarge hwhole i).length c : ℝ) :=
  (normalizedMesh_scale_lower hdelta hinv (hscale i)).trans
    (normalizedBoxPartitions_lengths N scale delta hlarge hwhole i c).1

end Erdos3

end

end OAI
