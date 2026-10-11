import GowersSzemeredi.Proofs18PolyDegrees
import GowersSzemeredi.Proofs18GradedDegrees
import GowersSzemeredi.Proofs18TheoremOneLinear
import GowersSzemeredi.Proofs16PhasePartitionOne
import GowersSzemeredi.Proofs16SimultaneousRecurrence
import GowersSzemeredi.Proofs16AllDimensionsExplicit

/-! **Theorem 18.1 at every degree up to eight.**

This module is a bridge. The light modules prove Theorem 18.1 at degree
three (`theorem_18_1_three_of_phase_partition`) and at degrees four to seven
(`theorem_18_1_four_to_seven_of_profiles`). They assume:
* a phase partition of progressions with `K ≤ 2^p` and `p ≤ 2^(2^64)`;
* for degrees four to eight, also the recurrence profiles.
Degree eight uses the graded vertex providers (`theorem_18_1_four_to_eight_of_profiles`).

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

/-- The dimension-one common-difference partition at the explicit constants. -/
theorem commonDiffPartitionOne_explicit :
    CommonDiffPartitionOne (multiaffinePartitionK 2 (2 ^ 2)) (multiaffinePartitionP 2 (2 ^ 2)) :=
  commonDiffPartitionBoundAt_of 1 (two_le_multiaffinePartitionK 2 _) (multiaffinePartitionP_pos 2 _)
    (multilinearPartitionBoundAt_explicit 2 (by norm_num))

/-- **A phase partition of progressions** with the constants Lemma 13.5 needs. -/
theorem progressionPhasePartition_explicit :
    ∃ (K : Real) (p : Nat), ProgressionPhasePartition K p ∧ 0 < p ∧ K ≤ 2 ^ p ∧
      (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64) := by
  have hconst : ((⌈multiaffinePartitionK 2 (2 ^ 2)⌉₊ : Nat) : Real) +
      ((2 * multiaffinePartitionP 2 (2 ^ 2) : Nat) : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64) := by
    have h := explicit_family_constants_le 1
    rw [show (1 : Nat) + 1 = 2 from rfl, show (1 : Nat) + 5 = 6 from rfl,
      show (2 : Nat) ^ 6 = 64 by norm_num] at h
    exact h
  have hK0 : multiaffinePartitionK 2 (2 ^ 2) ≤ (2 : Real) ^ ((2 : Nat) ^ 64) := by
    have h1 := Nat.le_ceil (multiaffinePartitionK 2 (2 ^ 2))
    have h2 : (0 : Real) ≤ ((2 * multiaffinePartitionP 2 (2 ^ 2) : Nat) : Real) := Nat.cast_nonneg _
    linarith only [h1, h2, hconst]
  have hp0 : (multiaffinePartitionP 2 (2 ^ 2) : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64) := by
    have h1 := Nat.cast_nonneg (α := Real) ⌈multiaffinePartitionK 2 (2 ^ 2)⌉₊
    have h2 : ((2 * multiaffinePartitionP 2 (2 ^ 2) : Nat) : Real) =
        2 * (multiaffinePartitionP 2 (2 ^ 2) : Real) := by push_cast; ring
    have h3 : (0 : Real) ≤ (multiaffinePartitionP 2 (2 ^ 2) : Real) := Nat.cast_nonneg _
    linarith only [h1, h2, h3, hconst]
  have h64 : (2 : Real) ^ (64 : Nat) ≤ (2 : Real) ^ ((2 : Nat) ^ 64) :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  refine ⟨multiaffinePartitionK 2 (2 ^ 2), max (multiaffinePartitionP 2 (2 ^ 2)) (2 ^ 64),
    (progressionPhasePartition_of_commonDiffOne commonDiffPartitionOne_explicit).mono
      (le_max_left _ _),
    lt_of_lt_of_le (multiaffinePartitionP_pos 2 _) (le_max_left _ _),
    hK0.trans (pow_le_pow_right₀ (by norm_num) (le_max_right _ _)), ?_⟩
  have hcast : ((max (multiaffinePartitionP 2 (2 ^ 2)) (2 ^ 64) : Nat) : Real) =
      max (multiaffinePartitionP 2 (2 ^ 2) : Real) ((2 : Real) ^ (64 : Nat)) := by
    simp only [Nat.cast_max, Nat.cast_pow, Nat.cast_ofNat]
  rw [hcast]
  exact max_le hp0 h64

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

/-- **Theorem 18.1 at degrees four to eight**, with graded vertex providers. -/
theorem theorem_18_1_four_to_eight {d : Nat} (hd4 : 4 ≤ d) (hd8 : d ≤ 8) : Theorem181At d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_four_to_eight_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd4 hd8

/-- **Theorem 18.1 at every degree up to eight.** -/
theorem theorem_18_1_le_eight {d : Nat} (hd : d ≤ 8) : Theorem181At d := by
  rcases Nat.lt_or_ge d 4 with h | h
  · exact theorem_18_1_le_seven (by omega)
  · exact theorem_18_1_four_to_eight h hd

end LeanProofs.GowersSzemeredi
