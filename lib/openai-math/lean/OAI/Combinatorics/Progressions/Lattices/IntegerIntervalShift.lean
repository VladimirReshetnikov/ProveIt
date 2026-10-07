import OAI.Combinatorics.Progressions.Estimates.ShiftDifferenceCount

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_interval_shift (f : ℤ → ℂ) {N H : ℕ}
    (hN : 0 < N) (hH : H ≤ N)
    (hsupport : ∀ x, x ∉ Finset.Ico (0 : ℤ) (N : ℤ) → f x = 0)
    (hf : ∀ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * H)
    (hscore : δ * N ≤ ‖∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), f x‖) :
    ∃ h : ℤ, h ≠ 0 ∧ |h| < (H : ℤ) ∧
      δ ^ 2 * N / 4 ≤ ‖shiftCorrelation (Finset.Ico (0 : ℤ) (N : ℤ)) f h‖ := by
  let Q := Finset.Ico (0 : ℤ) (N : ℤ)
  let S := Finset.Ico (0 : ℤ) (H : ℤ)
  let T := Finset.Ico (0 : ℤ) ((N + H : ℕ) : ℤ)
  have hQ : Q.Nonempty := Finset.nonempty_Ico.mpr (by exact_mod_cast hN)
  have hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T := by
    intro s hs x hx
    simp only [S, Q, T, Finset.mem_Ico, Nat.cast_add] at *
    omega
  have hT : T.card ≤ 2 * Q.card := by
    simp only [T, Q, Int.card_Ico, sub_zero, Int.toNat_natCast]
    omega
  obtain ⟨s, hs, t, ht, hst, hcorr⟩ := exists_large_shift_pair Q T S f hQ hsupport hf hcover hT
    hδ (by simpa only [S, Int.card_Ico, sub_zero, Int.toNat_natCast] using hshift)
    (by simpa only [Q, Int.card_Ico, sub_zero, Int.toNat_natCast] using hscore)
  refine ⟨s - t, sub_ne_zero.mpr hst, ?_, ?_⟩
  · simp only [S, Finset.mem_Ico] at hs ht
    rw [abs_lt]
    omega
  · simpa only [Q, Int.card_Ico, sub_zero, Int.toNat_natCast] using hcorr

theorem many_large_interval_shifts (f : ℤ → ℂ) {N H : ℕ}
    (hN : 0 < N) (hH : H ≤ N)
    (hsupport : ∀ x, x ∉ Finset.Ico (0 : ℤ) (N : ℤ) → f x = 0)
    (hf : ∀ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hshift : 8 ≤ δ ^ 2 * H)
    (hscore : δ * N ≤ ‖∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), f x‖) :
    ∃ D : Finset ℤ, δ ^ 2 * H / 8 ≤ (D.card : ℝ) ∧
      ∀ h ∈ D, h ≠ 0 ∧ |h| < (H : ℤ) ∧
        δ ^ 2 * N / 8 ≤ ‖shiftCorrelation (Finset.Ico (0 : ℤ) (N : ℤ)) f h‖ := by
  let Q := Finset.Ico (0 : ℤ) (N : ℤ)
  let S := Finset.Ico (0 : ℤ) (H : ℤ)
  let T := Finset.Ico (0 : ℤ) ((N + H : ℕ) : ℤ)
  have hQ : Q.Nonempty := Finset.nonempty_Ico.mpr (by exact_mod_cast hN)
  have hcover : ∀ s ∈ S, ∀ x ∈ Q, x + s ∈ T := by
    intro s hs x hx
    simp only [S, Q, T, Finset.mem_Ico, Nat.cast_add] at *
    omega
  have hT : T.card ≤ 2 * Q.card := by
    simp only [T, Q, Int.card_Ico, sub_zero, Int.toNat_natCast]
    omega
  obtain ⟨D, hD, hgood⟩ := many_large_shift_differences Q T S f hQ hsupport hf hcover hT
    hδ (by simpa only [S, Int.card_Ico, sub_zero, Int.toNat_natCast] using hshift)
    (by simpa only [Q, Int.card_Ico, sub_zero, Int.toNat_natCast] using hscore)
  refine ⟨D, ?_, ?_⟩
  · simpa only [S, Int.card_Ico, sub_zero, Int.toNat_natCast] using hD
  · intro h hh
    obtain ⟨hne, ⟨s, hs, t, ht, rfl⟩, hcorr⟩ := hgood h hh
    refine ⟨hne, ?_, ?_⟩
    · simp only [S, Finset.mem_Ico] at hs ht
      rw [abs_lt]
      omega
    · simpa only [Q, Int.card_Ico, sub_zero, Int.toNat_natCast] using hcorr

end Erdos3

end

end OAI
