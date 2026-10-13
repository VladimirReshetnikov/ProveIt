import GowersSzemeredi.Proofs16ExplicitPhasePartition
import GowersSzemeredi.Proofs18PolyDegrees
import GowersSzemeredi.Proofs18GradedDegrees
import GowersSzemeredi.Proofs18TheoremOneLinear

/-! **Theorem 18.1 at every degree up to nine.**

This module is a bridge. The light modules prove Theorem 18.1 at degree
three (`theorem_18_1_three_of_phase_partition`) and at degrees four to seven
(`theorem_18_1_four_to_seven_of_profiles`). They assume:
* a phase partition of progressions with `K ≤ 2^p` and `p ≤ 2^(2^64)`;
* for degrees four to nine, also the recurrence profiles.
Degrees eight and nine use the graded vertex providers
(`theorem_18_1_four_to_nine_of_profiles`).

Both are supplied here at explicit constants.
* The explicit multilinear partition in dimension two gives
  `CommonDiffPartitionBoundAt 1` at `K = multiaffinePartitionK 2 4` and
  `p = multiaffinePartitionP 2 4` (`commonDiffPartitionOne_explicit`).
  - `explicit_family_constants_le 1` bounds `⌈K⌉ + 2p ≤ 2^(2^64)`.
  - Raising `p` to `max p 2^64` gives `K ≤ 2^p`
    (`progressionPhasePartition_explicit`).
* The profiles are those of `theorem_18_2_six_to_ten`.

Degrees zero, one and two are the corpus's.

The imports reach the port's Schmidt constants, so this module is checked
on the full-verification host. Every step is an instantiation of a
kernel-checked statement. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.1 at degree three**, at the source's exponent
`α^(2^(2^13))`. -/
theorem theorem_18_1_three : Theorem181At 3 := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_three_of_phase_partition hpp hp hK hpB

/-- **Theorem 18.1 at degrees four to seven.** -/
theorem theorem_18_1_four_to_seven {d : Nat} (hd4 : 4 ≤ d) (hd7 : d ≤ 7) : Theorem181At d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_four_to_seven_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd4 hd7

/-- **Theorem 18.1 at every degree up to seven.** -/
theorem theorem_18_1_le_seven {d : Nat} (hd : d ≤ 7) : Theorem181At d := by
  rcases Nat.lt_or_ge d 4 with h | h
  · interval_cases d
    · exact theorem_18_1_degree_zero
    · exact theorem_18_1_degree_one
    · exact theorem_18_1_degree_two
    · exact theorem_18_1_three
  · exact theorem_18_1_four_to_seven h hd

/-- **Theorem 18.1 at degrees four to nine**, with graded vertex providers. -/
theorem theorem_18_1_four_to_nine {d : Nat} (hd4 : 4 ≤ d) (hd9 : d ≤ 9) : Theorem181At d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_four_to_nine_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd4 hd9

/-- **Theorem 18.1 at every degree up to nine.** -/
theorem theorem_18_1_le_nine {d : Nat} (hd : d ≤ 9) : Theorem181At d := by
  rcases Nat.lt_or_ge d 4 with h | h
  · exact theorem_18_1_le_seven (by omega)
  · exact theorem_18_1_four_to_nine h hd

/-- Theorem 18.1 at every degree up to eight. -/
theorem theorem_18_1_le_eight {d : Nat} (hd : d ≤ 8) : Theorem181At d :=
  theorem_18_1_le_nine (by omega)

end LeanProofs.GowersSzemeredi
