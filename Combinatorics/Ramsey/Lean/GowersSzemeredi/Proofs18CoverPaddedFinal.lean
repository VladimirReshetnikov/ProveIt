import GowersSzemeredi.Proofs18CoverLongThresholds
import GowersSzemeredi.Proofs16ExplicitRecurrenceProfiles

/-! The printed final bound from one uniform long-progression argument.

The improved `L+5` threshold at `L=max(k,6)` fits the printed `k+9`
threshold for every k>=2. Taking a prefix replaces the separate short-length
theorems; the one-term case only needs a point of the positive-density set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The printed bound needs only the improved theorem at lengths at least six. -/
theorem theorem_18_2_of_long_progressions
    (hlong : ∀ L : Nat, 6 ≤ L → Theorem182AtSharp 5 L) : theorem_18_2 := by
  intro delta k N hd hdHalf hk hN A hA hcard
  by_cases hkOne : k = 1
  · subst k
    have hNpos : (0 : Real) < N :=
      (show 0 < szemerediThreshold delta 1 by unfold szemerediThreshold; positivity).trans_le hN
    have hcardpos : 0 < A.card := by
      exact_mod_cast (mul_pos hd hNpos).trans_le hcard
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardpos
    refine ⟨a, 1, by decide, ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    simpa [hi0] using ha
  have hdOne : 1 ≤ delta⁻¹ := (one_le_inv₀ hd).mpr (by linarith)
  have hshift : max k 6 + 5 ≤ k + 9 := by omega
  have hthreshold : szemerediThresholdAt 5 delta (max k 6) ≤ szemerediThreshold delta k := by
    unfold szemerediThresholdAt szemerediThreshold
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply Real.rpow_le_rpow_of_exponent_le hdOne
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact pow_le_pow_right₀ (by norm_num) hshift
  obtain ⟨a, d, hd, hmem⟩ := hlong (max k 6) (le_max_right _ _) delta N hd hdHalf
    (hthreshold.trans hN) A hA hcard
  exact ⟨a, d, hd, fun i hi => hmem i (hi.trans_le (le_max_left _ _))⟩

/-- Theorem 18.2 with its original statement and threshold, using only the
general cover at lengths at least six and taking progression prefixes. -/
theorem theorem_18_2_padded : theorem_18_2 :=
  theorem_18_2_of_long_progressions fun _ hL =>
    theorem_18_2_L5_all_of_profiles_cover
      (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
      (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
      (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
      (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
      (fun k _ => section16RecurrenceProfileWith_explicit k)
      explicit_family_constants_le hL

end LeanProofs.GowersSzemeredi
