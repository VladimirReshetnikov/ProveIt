import GowersSzemeredi.Proofs18CoverSharperExplicit
import GowersSzemeredi.Proofs18CoverSharperLowDegrees

/-! **Theorem 18.1 in every degree with exponent `α^(2^(2^(d+7)))`** (Notes L.15c).

Degrees `0, 1, 2` from the corpus proofs with the sharper constant, degree
three from the polynomial base envelope at the explicit phase partition, and
degrees `d ≥ 4` from the tight-base envelope (`theorem_18_1_d7_four_le`).
At `c = 10` the statement is the catalogue's Theorem 18.1
(`theorem181AtSharp_ten_iff`), so this strengthens `theorem_18_1_explicit`
(`theorem_18_1_d7_implies_printed`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.1 at every degree with `d + 7` in place of `d + 10`.** -/
theorem theorem_18_1_d7 (d : Nat) : Theorem181AtSharp 7 d := by
  match d with
  | 0 => exact theorem_18_1_d7_degree_zero
  | 1 => exact theorem_18_1_d7_degree_one
  | 2 => exact theorem_18_1_d7_degree_two
  | 3 =>
    obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
    exact theorem_18_1_d7_three_of_phase_partition hpp hp hK hpB
  | d + 4 => exact theorem_18_1_d7_four_le (by omega)

/-- The sharper statement implies the catalogue's Theorem 18.1. -/
theorem theorem_18_1_d7_implies_printed : theorem_18_1 :=
  theorem_18_1_iff_forall_degree.mpr fun d =>
    (theorem181AtSharp_ten_iff d).mp ((theorem_18_1_d7 d).mono (by norm_num))

end LeanProofs.GowersSzemeredi
