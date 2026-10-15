import GowersSzemeredi.Proofs18CoverSharperLowDegrees
import GowersSzemeredi.Proofs03FourFactorSymmetry
import GowersSzemeredi.Proofs05Corollary58
import GowersSzemeredi.Proofs05HighCorrelationAssembly
import GowersSzemeredi.Proofs05HighCorrelationScale
import GowersSzemeredi.Proofs05ThresholdFreeScale

/-! **Theorem 18.1 with offset six in degrees zero through three.**

Each statement follows by monotonicity from the shared offset-four proof
in `Proofs18CoverSharperLowDegrees`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem theorem_18_1_d6_degree_zero : Theorem181AtSharp 6 0 :=
  theorem_18_1_d4_degree_zero.mono (by norm_num)

theorem section18ExponentAt6_two_le_quadraticDiscrepancyParameter {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 6 alpha 2 ≤ quadraticDiscrepancyParameter alpha := by
  exact (section18ExponentAt_antitone (by norm_num : 4 ≤ 6) hα.le (by linarith)).trans
    (section18ExponentAt4_two_le_quadraticDiscrepancyParameter hα hα2)

theorem section18ExponentAt6_two_le_quadraticDiscrepancyExponent {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 6 alpha 2 ≤ quadraticDiscrepancyExponent alpha := by
  exact (section18ExponentAt_antitone (by norm_num : 4 ≤ 6) hα.le (by linarith)).trans
    (section18ExponentAt4_two_le_quadraticDiscrepancyExponent hα hα2)

theorem theorem_18_1_d6_degree_two : Theorem181AtSharp 6 2 :=
  theorem_18_1_d4_degree_two.mono (by norm_num)

theorem theorem_18_1_d6_degree_one : Theorem181AtSharp 6 1 :=
  theorem_18_1_d4_degree_one.mono (by norm_num)

/-- **Theorem 18.1 at degree three with exponent `α^(2^(2^9))`**, from a phase
partition. -/
theorem theorem_18_1_d6_three_of_phase_partition
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    Theorem181AtSharp 6 3 :=
  (theorem_18_1_d4_three_of_phase_partition hpp hpφ hKφ hpφB).mono (by norm_num)

end LeanProofs.GowersSzemeredi
