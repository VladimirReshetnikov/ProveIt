import GowersSzemeredi.Proofs16MixedCorrelation

/-! The mixed Fourier mass outside an intersection of large spectra. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def commonLargeSpectrum {N : Nat} [NeZero N] (A B : Finset (ZMod N)) (tau : Real) :
    Finset (ZMod N) := Finset.univ.filter fun r =>
      tau * N ≤ ‖fourier (indicator A) r‖ ∧ tau * N ≤ ‖fourier (indicator B) r‖

/-- Parseval for a finite set indicator. -/
theorem indicator_fourier_energy {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    (∑ r : ZMod N, ‖fourier (indicator A) r‖^2) = N * (A.card : Real) := by
  rw [identity_2_3_holds]
  congr 1
  have hnorm (x : ZMod N) : ‖indicator A x‖^2 = if x ∈ A then (1 : Real) else 0 := by
    by_cases hx : x ∈ A <;> simp [indicator, hx]
  simp only [hnorm]
  simp

/-- A small coefficient in either factor makes its product weight small. -/
theorem mixedFourierWeight_small {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) {tau : Real} (htau : 0 ≤ tau) (r : ZMod N)
    (hr : r ∉ commonLargeSpectrum A B tau) :
    mixedFourierWeight A B r ≤ (tau * N)^2 *
      (‖fourier (indicator A) r‖^2 + ‖fourier (indicator B) r‖^2) := by
  have hnot : ¬ (tau * N ≤ ‖fourier (indicator A) r‖ ∧ tau * N ≤ ‖fourier (indicator B) r‖) := by
    simpa only [commonLargeSpectrum, Finset.mem_filter, Finset.mem_univ, true_and] using hr
  have ht : 0 ≤ tau * N := by positivity
  unfold mixedFourierWeight
  by_cases hA : tau * N ≤ ‖fourier (indicator A) r‖
  · have hB : ‖fourier (indicator B) r‖ ≤ tau * N := le_of_lt (lt_of_not_ge (fun hB => hnot ⟨hA, hB⟩))
    have hs : ‖fourier (indicator B) r‖^2 ≤ (tau * N)^2 := by nlinarith [norm_nonneg (fourier (indicator B) r)]
    have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg ‖fourier (indicator A) r‖)
    have hpos := mul_nonneg (sq_nonneg (tau * N)) (sq_nonneg ‖fourier (indicator B) r‖)
    nlinarith only [hmul, hpos]
  · have hs : ‖fourier (indicator A) r‖^2 ≤ (tau * N)^2 := by
      have := le_of_lt (lt_of_not_ge hA)
      nlinarith [norm_nonneg (fourier (indicator A) r)]
    have hmul := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖fourier (indicator B) r‖)
    have hpos := mul_nonneg (sq_nonneg (tau * N)) (sq_nonneg ‖fourier (indicator A) r‖)
    nlinarith only [hmul, hpos]

/-- The exceptional mixed mass has a bound retaining both set densities. -/
theorem mixedFourierWeight_tail_le {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) {tau : Real} (htau : 0 ≤ tau) :
    (∑ r ∈ Finset.univ \ commonLargeSpectrum A B tau, mixedFourierWeight A B r) ≤
      tau^2 * (N : Real)^3 * (A.card + B.card : Real) := by
  calc
    _ ≤ ∑ r ∈ Finset.univ \ commonLargeSpectrum A B tau,
        (tau * N)^2 * (‖fourier (indicator A) r‖^2 + ‖fourier (indicator B) r‖^2) :=
      Finset.sum_le_sum fun r hr => mixedFourierWeight_small A B htau r (Finset.mem_sdiff.mp hr).2
    _ ≤ ∑ r : ZMod N,
        (tau * N)^2 * (‖fourier (indicator A) r‖^2 + ‖fourier (indicator B) r‖^2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro r _ _
      positivity
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, indicator_fourier_energy, indicator_fourier_energy]
      ring

/-- A density-free simplification of the exceptional-mass bound. -/
theorem mixedFourierWeight_tail_le_universal {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) {tau : Real} (htau : 0 ≤ tau) :
    (∑ r ∈ Finset.univ \ commonLargeSpectrum A B tau, mixedFourierWeight A B r) ≤
      2 * tau^2 * (N : Real)^4 := by
  have hA : (A.card : Real) ≤ N := by exact_mod_cast (show A.card ≤ N by simpa using Finset.card_le_univ A)
  have hB : (B.card : Real) ≤ N := by exact_mod_cast (show B.card ≤ N by simpa using Finset.card_le_univ B)
  have h := mul_le_mul_of_nonneg_left (add_le_add hA hB) (show 0 ≤ tau^2 * (N : Real)^3 by positivity)
  have ht := mixedFourierWeight_tail_le A B htau
  nlinarith only [ht, h]

end LeanProofs.GowersSzemeredi
