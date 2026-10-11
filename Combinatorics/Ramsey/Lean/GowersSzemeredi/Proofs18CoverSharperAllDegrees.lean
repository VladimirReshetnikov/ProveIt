import GowersSzemeredi.Proofs18CoverSharperExplicit
import GowersSzemeredi.Proofs18CoverSharperLowDegrees
import GowersSzemeredi.Proofs18CoverSharperShortLengths
import GowersSzemeredi.Proofs18CoverThresholdsSharp

/-! **Theorem 18.1 in every degree with exponent `α^(2^(2^(d+7)))`** (Notes L.15c).

Degrees `0, 1, 2` from the corpus proofs with the sharper constant, degree
three from the polynomial base envelope at the explicit phase partition, and
degrees `d ≥ 4` from the tight-base envelope (`theorem_18_1_d7_four_le`).
At `c = 10` the statement is the catalogue's Theorem 18.1
(`theorem181AtSharp_ten_iff`), so this strengthens `theorem_18_1_explicit`
(`theorem_18_1_d7_implies_printed`).

Likewise Theorem 18.2 and Corollary 18.7 with `L + 6` in place of `L + 9`
in every length (`theorem_18_2_L6`, `corollary_18_7_L6`): lengths `L ≤ 5`
from the corpus's explicit thresholds (`Proofs18CoverSharperShortLengths`),
lengths `L ≥ 6` from the joint-cover envelope.

With the phase-refinement threshold at the exponential level
(`Proofs18CoverThresholdsSharp`), even `L + 5` holds in every length
(`theorem_18_2_L5`, `corollary_18_7_L5`). -/
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

/-- **Theorem 18.2 at every length with `L + 6` in place of `L + 9`.** -/
theorem theorem_18_2_L6 (L : Nat) : Theorem182AtSharp 6 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L6_le_five (by omega)
  · exact theorem_18_2_sharper_six_le h

/-- **Corollary 18.7 at every length with `L + 6` in place of `L + 9`.** -/
theorem corollary_18_7_L6 (L : Nat) : Corollary187AtSharp 6 L :=
  (theorem_18_2_L6 L).corollary_18_7

/-- The sharper statement implies the catalogue's Theorem 18.2. -/
theorem theorem_18_2_L6_implies_printed : theorem_18_2 :=
  theorem_18_2_iff_forall_length.mpr fun L _ =>
    (theorem182AtSharp_nine_iff L).mp ((theorem_18_2_L6 L).mono (by norm_num))

/-- The sharper statement implies the catalogue's Corollary 18.7. -/
theorem corollary_18_7_L6_implies_printed : corollary_18_7 :=
  corollary_18_7_iff_forall_length.mpr fun L _ =>
    (corollary187AtSharp_nine_iff L).mp (((theorem_18_2_L6 L).mono (by norm_num)).corollary_18_7)

/-- **Theorem 18.2 at every length with `L + 5` in place of `L + 9`.** -/
theorem theorem_18_2_L5 (L : Nat) : Theorem182AtSharp 5 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L5_le_five (by omega)
  · exact theorem_18_2_L5_all_of_profiles_cover
      (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
      (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
      (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
      (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
      (fun k _ => section16RecurrenceProfileWith_explicit k)
      (fun k => explicit_family_constants_le k) h

/-- **Corollary 18.7 at every length with `L + 5` in place of `L + 9`.** -/
theorem corollary_18_7_L5 (L : Nat) : Corollary187AtSharp 5 L :=
  (theorem_18_2_L5 L).corollary_18_7

end LeanProofs.GowersSzemeredi
