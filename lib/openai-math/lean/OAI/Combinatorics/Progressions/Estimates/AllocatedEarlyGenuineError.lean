import OAI.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

theorem allocatedEarlySpatialFactor_exp_bound (dim : ℕ) (X : Type*) [Fintype X]
    {Pearly Psp : ℝ} (hPearly : 0 ≤ Pearly) (hPsp : 0 ≤ Psp)
    (hcount : Pearly ≤ Real.exp Psp) (hdim : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (hX : (Fintype.card X : ℝ) ≤ Psp) :
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      ((Pearly + 1) ^ dim) ^ Fintype.card X ≤ Real.exp (coefficientErrorVolumeLog Psp) := by
  simpa only [div_one, add_comm] using
    referenceErrorVolumeFactor_exp_bound dim X hPsp hdim hX
      (le_refl (1 : ℝ)) hPearly hcount (by simp : Pearly ≤ Pearly * 1)

def allocatedEarlyGenuineErrorLog (Psp s c a v E : ℝ) : ℝ :=
  s + c + a + coefficientErrorVolumeLog Psp + v + E + 1

theorem allocatedEarlyGenuineErrorLog_nonneg {Psp s c a v E : ℝ}
    (hPsp : 0 ≤ Psp) (hs : 0 ≤ s) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedEarlyGenuineErrorLog Psp s c a v E := by
  unfold allocatedEarlyGenuineErrorLog coefficientErrorVolumeLog
  positivity

theorem allocatedEarlyGenuineError_exp_bound (dim : ℕ) (X : Type*) [Fintype X]
    {Pearly Psp Csp Cgrid Cmask Vmass Z s c a v E : ℝ}
    (hPearly : 0 ≤ Pearly) (hPsp : 0 ≤ Psp) (hcount : Pearly ≤ Real.exp Psp)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ Psp) (hX : (Fintype.card X : ℝ) ≤ Psp)
    (hCgrid : 0 ≤ Cgrid) (hCmask : 0 ≤ Cmask) (hVmass : 0 ≤ Vmass)
    (hs : Csp ≤ Real.exp s) (hc : Cgrid ≤ Real.exp c)
    (ha : Cmask ≤ Real.exp a) (hv : Vmass ≤ Real.exp v)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2) :
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      ((Pearly + 1) ^ dim) ^ Fintype.card X
    ((Csp * Cgrid) * (Cmask * Real.exp (-allocatedEarlyGenuineErrorLog Psp s c a v E)) *
      (factor * Vmass)) / Z ≤ Real.exp (-E) := by
  intro factor
  have hfactor : factor ≤ Real.exp (coefficientErrorVolumeLog Psp) :=
    allocatedEarlySpatialFactor_exp_bound dim X hPearly hPsp hcount hdim hX
  have hfactor0 : 0 ≤ factor := by
    have hprofile := smoothProbabilityProfile_pos_zero
    dsimp [factor]
    positivity
  have hprod : (Csp * Cgrid) *
      (Cmask * Real.exp (-allocatedEarlyGenuineErrorLog Psp s c a v E)) *
      (factor * Vmass) ≤ Real.exp (-(E + 1)) := by
    calc
      _ ≤ (Real.exp s * Real.exp c) *
          (Real.exp a * Real.exp (-allocatedEarlyGenuineErrorLog Psp s c a v E)) *
          (Real.exp (coefficientErrorVolumeLog Psp) * Real.exp v) := by gcongr
      _ = _ := by
        simp only [← Real.exp_add]
        congr 1
        unfold allocatedEarlyGenuineErrorLog
        ring
  calc
    _ = ((Csp * Cgrid) * (Cmask * Real.exp (-allocatedEarlyGenuineErrorLog Psp s c a v E)) *
        (factor * Vmass)) * Z⁻¹ := div_eq_mul_inv _ _
    _ ≤ Real.exp (-(E + 1)) * 2 :=
      mul_le_mul hprod hZi (inv_nonneg.mpr hZ.le) (Real.exp_pos _).le
    _ ≤ Real.exp (-(E + 1)) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
