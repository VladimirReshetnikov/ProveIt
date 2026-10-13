import GowersSzemeredi.Proofs16PhasePartitionOne
import GowersSzemeredi.Proofs16ExplicitRecurrenceProfiles

/-! The explicit progression phase-partition input shared by the final bounds. -/
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

end LeanProofs.GowersSzemeredi
