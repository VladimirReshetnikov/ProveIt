import GowersSzemeredi.Proofs16DirectionalBohrSpan

/-! Uniform bounded frequency alphabets obtained from dense rows of the
original set. These provide the geometric input to the selection stage. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Choose the row Bogolyubov spectra with one density-dependent rank cap.
Rows outside Y receive the empty spectrum. -/
theorem dense_row_spectra {N : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    {delta : Real} (hdelta : 0 < delta)
    (hdense : ∀ y ∈ Y, delta ≤ (rowOf A y).card / (N : Real)) :
    ∃ Gamma : ZMod N → Finset (ZMod N),
      (∀ y, (Gamma y).card ≤ ⌈16 * delta ^ (-(2 : Real))⌉₊) ∧
      ∀ y ∈ Y, ∀ x ∈ bohr (Gamma y) (1 / (8 * Real.pi)),
        (x, y) ∈ horDiff (horDiff A) := by
  have hex (y : ZMod N) : ∃ K : Finset (ZMod N),
      K.card ≤ ⌈16 * delta ^ (-(2 : Real))⌉₊ ∧
      (y ∈ Y → ∀ x ∈ bohr K (1 / (8 * Real.pi)), (x, y) ∈ horDiff (horDiff A)) := by
    by_cases hy : y ∈ Y
    · have hpos : 0 < (rowOf A y).card / (N : Real) := hdelta.trans_le (hdense y hy)
      have hrow : (rowOf A y).Nonempty := by
        apply Finset.card_pos.mp
        by_contra hcard
        have hz := Nat.eq_zero_of_not_pos hcard
        simp [hz] at hpos
      obtain ⟨K, hK, hB⟩ := row_bogolyubov A y hrow
      refine ⟨K, ?_, fun _ => hB⟩
      have hpow := Real.rpow_le_rpow_of_nonpos hdelta (hdense y hy) (by norm_num : -(2 : Real) ≤ 0)
      have hbound : (K.card : Real) ≤ 16 * delta ^ (-(2 : Real)) :=
        hK.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
      exact_mod_cast hbound.trans (Nat.le_ceil _)
    · exact ⟨∅, by simp, fun h => (hy h).elim⟩
  choose Gamma hGamma hrows using hex
  exact ⟨Gamma, hGamma, hrows⟩

/-- Dense rows produce finite alphabets containing zero and controlling the
four-direction difference set, uniformly in the prime modulus. -/
theorem dense_row_directional_alphabets {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    {delta : Real} (hdelta : 0 < delta)
    (hdense : ∀ y ∈ Y, delta ≤ (rowOf A y).card / (N : Real))
    (M : Nat) [NeZero M] (hM : 2 ≤ (1 / (8 * Real.pi)) * M) :
    ∃ U : ZMod N → Finset (ZMod N),
      (∀ y, (0 : ZMod N) ∈ U y ∧
        (U y).card ≤ (2 * directionalSpanCutoff ⌈16 * delta ^ (-(2 : Real))⌉₊ M
          (1 / (8 * Real.pi)) + 1) ^ ⌈16 * delta ^ (-(2 : Real))⌉₊) ∧
      ∀ y z w d : ZMod N, y + z ∈ Y → z ∈ Y → y + w ∈ Y → w ∈ Y →
        d ∈ bohr (frequencyDifference (U (y + z)) (U z) ∩
          frequencyDifference (U (y + w)) (U w)) (1 / (4 * Real.pi)) →
        (d, y) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  obtain ⟨Gamma, hGamma, hrows⟩ := dense_row_spectra A Y hdelta hdense
  let r := ⌈16 * delta ^ (-(2 : Real))⌉₊
  refine ⟨rowSpanAlphabet Gamma (directionalSpanCutoff r M (1 / (8 * Real.pi))),
    rowSpanAlphabet_bounds Gamma r _ hGamma, ?_⟩
  intro y z w d hyz hz hyw hw hd
  exact directional_bohr_span (horDiff (horDiff A)) Y Gamma r M hGamma
    (by positivity) (by have := Real.pi_gt_three; rw [div_lt_one (by positivity)]; linarith)
    hM hrows y z w d hyz hz hyw hw hd

end LeanProofs.GowersSzemeredi
