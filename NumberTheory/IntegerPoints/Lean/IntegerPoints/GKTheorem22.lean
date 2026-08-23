import IntegerPoints.GKStatements
import IntegerPoints.GKHighCurvature

/-!
# Graham–Kolesnik, Theorem 2.2 in its two invoked forms

Both statements are immediate scale specializations of
`gk_high_curvature_bound`: `L < 1` removes `√L`, while `L < log N` replaces it
by `√(log N)`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

/-- **Graham–Kolesnik, Theorem 2.2**, in the form invoked in §3.3. -/
theorem gk_theorem22_invoked_sec33_holds : gk_theorem22_invoked_sec33 := by
  intro s ε hs hε hεhalf
  obtain ⟨C, hC0, hhigh⟩ := gk_high_curvature_bound s hs
  refine ⟨C, ?_⟩
  intro N y a b f hN hy hf hLhalf hLone
  have hraw := hhigh ε N y a b f hε hεhalf hN hy hf hLhalf
  have hsqrtL : Real.sqrt (y * N ^ (-s)) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hLone.le
  calc
    ‖∑ n ∈ intRange a b, e (f n)‖ ≤
        C * (Real.sqrt (y * N ^ (-s)) * Real.sqrt N) := hraw
    _ ≤ C * (1 * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsqrtL (Real.sqrt_nonneg N)) hC0
    _ = C * N ^ ((1 : ℝ) / 2) := by
      rw [one_mul, Real.sqrt_eq_rpow]

/-- **Graham–Kolesnik, Theorem 2.2**, in the form invoked in the proof of
Theorem 3.8. -/
theorem gk_theorem22_invoked_sec34_holds : gk_theorem22_invoked_sec34 := by
  intro s ε hs hε hεhalf
  obtain ⟨C, hC0, hhigh⟩ := gk_high_curvature_bound s hs
  refine ⟨C, ?_⟩
  intro N y a b f hN hy hf hLone hLlog
  have hLhalf : 1 / 2 ≤ y * N ^ (-s) := by linarith
  have hraw := hhigh ε N y a b f hε hεhalf hN hy hf hLhalf
  have hsqrtL :
      Real.sqrt (y * N ^ (-s)) ≤ Real.sqrt (Real.log N) :=
    Real.sqrt_le_sqrt hLlog.le
  calc
    ‖∑ n ∈ intRange a b, e (f n)‖ ≤
        C * (Real.sqrt (y * N ^ (-s)) * Real.sqrt N) := hraw
    _ ≤ C * (Real.sqrt (Real.log N) * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsqrtL (Real.sqrt_nonneg N)) hC0
    _ = C * (N ^ ((1 : ℝ) / 2) *
        (Real.log N) ^ ((1 : ℝ) / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      ring

end LeanProofs.IntegerPoints
