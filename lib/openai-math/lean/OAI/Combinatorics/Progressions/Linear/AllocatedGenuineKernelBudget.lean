import OAI.Combinatorics.Progressions.Dynamics.AllocatedFiniteIdealMaskBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def allocatedGenuineKernelErrorLog {A : Type*} [Semiring A] (m : ℕ) (D P : A) : A :=
  D * ((m * 2 ^ (m + 1) : ℕ) * P) + D ^ 3 * ((m + 1 : ℕ) * P)

theorem allocatedGenuineKernelErrorLog_nonneg (m : ℕ) {D P : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) :
    0 ≤ allocatedGenuineKernelErrorLog m D P := by
  unfold allocatedGenuineKernelErrorLog
  positivity

theorem allocatedGenuineKernelError_exp_bound {m : ℕ}
    (I : Fin m → Type*) [∀ j, Fintype (I j)] (n : Fin m → ℕ)
    (O K : Fin m → Type*) [∀ j, Fintype (O j)] [∀ j, Fintype (K j)]
    {M period : ℕ} {D P : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hM : (M : ℝ) ≤ Real.exp P) (hperiod : period ≤ M ^ (m + 1))
    (hm : (m : ℝ) ≤ D) (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (hO : ∀ j, (Fintype.card (O j) : ℝ) ≤ D)
    (hK : ∀ j, (Fintype.card (K j) : ℝ) ≤ D) :
    (layerKernelIndexBound m M : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap O K period ≤ Real.exp (allocatedGenuineKernelErrorLog m D P) := by
  have hindex := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg (layerKernelIndexBound m M))
    (layerKernelIndexBound_le_exp m hM) (by positivity) _ haxes
  have hperiodExp : (period : ℝ) ≤ Real.exp ((m + 1 : ℕ) * P) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiod
      _ ≤ (Real.exp P) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hdeck := coefficientDeckPeriodCap_exp_bound O K period hD (by positivity) hm hO hK hperiodExp
  exact (mul_le_mul hindex hdeck (coefficientDeckPeriodCap_nonneg O K period)
    (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm

end Erdos3.VectorPolynomial

end

end OAI
