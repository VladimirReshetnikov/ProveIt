import GowersSzemeredi.Proofs18CoverSharperLowDegrees

/-! Declarations of `Proofs18CoverSharperLowDegrees` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-! The older offset-seven interface follows from the offset-four result. -/

theorem theorem_18_1_d7_degree_zero : Theorem181AtSharp 7 0 :=
  theorem_18_1_d4_degree_zero.mono (by norm_num)

theorem section18ExponentAt7_two_le_quadraticDiscrepancyParameter {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 7 alpha 2 ≤ quadraticDiscrepancyParameter alpha := by
  exact (section18ExponentAt_antitone (by norm_num : 4 ≤ 7) hα.le (by linarith)).trans
    (section18ExponentAt4_two_le_quadraticDiscrepancyParameter hα hα2)

theorem section18ExponentAt7_two_le_quadraticDiscrepancyExponent {alpha : Real}
    (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2) :
    section18ExponentAt 7 alpha 2 ≤ quadraticDiscrepancyExponent alpha := by
  exact (section18ExponentAt_antitone (by norm_num : 4 ≤ 7) hα.le (by linarith)).trans
    (section18ExponentAt4_two_le_quadraticDiscrepancyExponent hα hα2)

theorem theorem_18_1_d7_degree_two : Theorem181AtSharp 7 2 :=
  theorem_18_1_d4_degree_two.mono (by norm_num)

theorem theorem_18_1_d7_degree_one : Theorem181AtSharp 7 1 :=
  theorem_18_1_d4_degree_one.mono (by norm_num)

/-- **Theorem 18.1 at degree three with exponent `α^(2^(2^10))`**, from a phase
partition. -/
theorem theorem_18_1_d7_three_of_phase_partition
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    Theorem181AtSharp 7 3 :=
  (theorem_18_1_d4_three_of_phase_partition hpp hpφ hKφ hpφB).mono (by norm_num)

end LeanProofs.GowersSzemeredi
