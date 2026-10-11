import GowersSzemeredi.Proofs18PolyCubicDegree
import GowersSzemeredi.Proofs16PhasePartitionOne
import GowersSzemeredi.Proofs16SimultaneousRecurrence
import GowersSzemeredi.Proofs16AllDimensionsExplicit

/-! **Theorem 18.1 at degree three.**

This module is a bridge. `theorem_18_1_three_of_phase_partition` (light,
kernel-checked locally) needs a phase partition of progressions with
`K ≤ 2^p` and `p ≤ 2^(2^64)`. The explicit multilinear partition in
dimension two gives `CommonDiffPartitionBoundAt 1` at
* `K = multiaffinePartitionK 2 4`;
* `p = multiaffinePartitionP 2 4`.

`explicit_family_constants_le 1` bounds `⌈K⌉ + 2p ≤ 2^(2^64)`. Raising `p` to
`max p 2^64` (`ProgressionPhasePartition.mono`) gives `K ≤ 2^p`.

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

/-- **Theorem 18.1 at degree three**, at the source's exponent
`α^(2^(2^13))`. -/
theorem theorem_18_1_three : Theorem181At 3 := by
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
  let p' := max (multiaffinePartitionP 2 (2 ^ 2)) (2 ^ 64)
  have hp'pos : 0 < p' := lt_of_lt_of_le (multiaffinePartitionP_pos 2 _) (le_max_left _ _)
  have hK : multiaffinePartitionK 2 (2 ^ 2) ≤ 2 ^ p' :=
    hK0.trans (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))
  have hpB : (p' : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64) := by
    have hcast : (p' : Real) = max (multiaffinePartitionP 2 (2 ^ 2) : Real) ((2 : Real) ^ (64 : Nat)) := by
      simp only [p', Nat.cast_max, Nat.cast_pow, Nat.cast_ofNat]
    rw [hcast]
    exact max_le hp0 h64
  exact theorem_18_1_three_of_phase_partition
    ((progressionPhasePartition_of_commonDiffOne commonDiffPartitionOne_explicit).mono
      (le_max_left _ _)) hp'pos hK hpB

end LeanProofs.GowersSzemeredi
