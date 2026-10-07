import OAI.Combinatorics.Progressions.Estimates.AllocatedSiteEnvelopeGain

namespace OAI

section

namespace Erdos3.VectorPolynomial

def siteReferenceMassLog {A : Type*} [Semiring A] (m : ℕ) (D P : A) : A :=
  coefficientErrorSpatialLog P + allocatedSiteEnvelopeMassLog m D P

def siteReferenceErrorLog {A : Type*} [Semiring A] (m : ℕ) (D P E : A) : A :=
  siteReferenceMassLog m D P + E + 2

noncomputable def siteReferenceAccuracy (m : ℕ) (D P E : ℝ) : ℝ :=
  Real.exp (-siteReferenceErrorLog m D P E)

theorem siteReferenceAccuracy_pos (m : ℕ) (D P E : ℝ) :
    0 < siteReferenceAccuracy m D P E := Real.exp_pos _

theorem siteReferenceMassLog_nonneg (m : ℕ) {D P : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) :
    0 ≤ siteReferenceMassLog m D P := by
  have hs := coefficientErrorSpatialLog_nonneg hP
  have hg := allocatedSiteEnvelopeGain_nonneg m hD hP
  unfold siteReferenceMassLog allocatedSiteEnvelopeMassLog
  positivity

theorem siteReference_error_le (m : ℕ) {D P E ε Z : ℝ}
    (hε : ε ≤ siteReferenceAccuracy m D P E) (hZ : 1 / 2 ≤ Z) :
    (ε * Real.exp (siteReferenceMassLog m D P)) / Z ≤ Real.exp (-E) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hid : siteReferenceAccuracy m D P E * Real.exp (siteReferenceMassLog m D P) =
      Real.exp (-E - 2) := by
    rw [siteReferenceAccuracy, ← Real.exp_add]
    congr 1
    unfold siteReferenceErrorLog
    ring
  have hsmall : ε * Real.exp (siteReferenceMassLog m D P) ≤ Real.exp (-E - 2) :=
    (mul_le_mul_of_nonneg_right hε (Real.exp_pos _).le).trans_eq hid
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hexp : 2 * Real.exp (-E - 2) ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-E - 2) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hzexp := mul_le_mul_of_nonneg_right hZ (Real.exp_pos (-E)).le
  apply (div_le_iff₀ hZ0).mpr
  nlinarith

end Erdos3.VectorPolynomial

end

end OAI
