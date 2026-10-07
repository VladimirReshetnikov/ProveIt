import OAI.Combinatorics.Progressions.Dynamics.AllocatedReferenceIdealBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

def allocatedSiteEnvelopeGain {A : Type*} [Semiring A] (m : ℕ) (D p : A) : A :=
  allocatedProfileGainLog m D p ((m * 2 ^ (m + 1) : ℕ) * p)

def allocatedSiteEnvelopeMassLog {A : Type*} [Semiring A] (m : ℕ) (D p : A) : A :=
  allocatedSiteEnvelopeGain m D p + D * ((m + 3 : ℕ) * D + 6) + 1

theorem allocatedSiteEnvelopeGain_nonneg (m : ℕ) {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) : 0 ≤ allocatedSiteEnvelopeGain m D p :=
  allocatedProfileGainLog_nonneg m hD hp (mul_nonneg (Nat.cast_nonneg _) hp)

theorem allocatedSiteEnvelope_sample_mass_le (m : ℕ) {D p A : ℝ} {N q : ℕ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hN : (N : ℝ) ≤ D) (hq : (q : ℝ) ≤ D)
    (hA : A ≤ Real.exp (allocatedSiteEnvelopeGain m D p)) :
    A * Real.exp ((N : ℝ) * (((m : ℝ) + 3) * q + 6)) + 2 * (1 / 4 : ℝ) + 1 / 4 ≤
      Real.exp (allocatedSiteEnvelopeMassLog m D p) := by
  let shape : ℝ := D * (((m : ℝ) + 3) * D + 6)
  have hs : 0 ≤ shape := by dsimp only [shape]; positivity
  have hg := allocatedSiteEnvelopeGain_nonneg m hD hp
  have hshape : (N : ℝ) * (((m : ℝ) + 3) * q + 6) ≤ shape := by
    dsimp only [shape]
    exact mul_le_mul hN (by gcongr) (by positivity) hD
  have hterm : A * Real.exp ((N : ℝ) * (((m : ℝ) + 3) * q + 6)) ≤
      Real.exp (allocatedSiteEnvelopeGain m D p + shape) := by
    calc
      _ ≤ Real.exp (allocatedSiteEnvelopeGain m D p) *
          Real.exp ((N : ℝ) * (((m : ℝ) + 3) * q + 6)) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
      _ ≤ Real.exp (allocatedSiteEnvelopeGain m D p) * Real.exp shape :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hshape) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hunit : 1 ≤ Real.exp (allocatedSiteEnvelopeGain m D p + shape) :=
    Real.one_le_exp_iff.mpr (add_nonneg hg hs)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2 * Real.exp (allocatedSiteEnvelopeGain m D p + shape) := by linarith
    _ ≤ Real.exp 1 * Real.exp (allocatedSiteEnvelopeGain m D p + shape) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      simp only [allocatedSiteEnvelopeMassLog, shape, Nat.cast_add, Nat.cast_ofNat]
      ring

end Erdos3.VectorPolynomial

end

end OAI
