import GowersSzemeredi.Proofs16PolynomialSpectrumSpan

/-! Mixed fourfold difference correlations. Their Fourier weights are
nonnegative products of squared Fourier magnitudes, so the intersection
of two large spectra controls a sum of two difference sets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def mixedDifferenceCorrelation {N : Nat} [NeZero N] (A B : Finset (ZMod N)) : ZMod N → Complex :=
  correlation (correlation (indicator A) (indicator A))
    (correlation (indicator B) (indicator B))

def mixedFourierWeight {N : Nat} [NeZero N] (A B : Finset (ZMod N)) (r : ZMod N) : Real :=
  ‖fourier (indicator A) r‖^2 * ‖fourier (indicator B) r‖^2

theorem mixedFourierWeight_nonneg {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (r : ZMod N) : 0 ≤ mixedFourierWeight A B r := by
  unfold mixedFourierWeight
  positivity

theorem fourier_mixedDifferenceCorrelation {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (r : ZMod N) :
    fourier (mixedDifferenceCorrelation A B) r = (mixedFourierWeight A B r : Complex) := by
  unfold mixedDifferenceCorrelation mixedFourierWeight
  rw [identity_2_1_holds, identity_2_1_holds, identity_2_1_holds]
  simp only [Complex.star_def, Complex.mul_conj', map_pow, Complex.conj_ofReal, Complex.ofReal_mul,
    Complex.ofReal_pow]

theorem mixedDifferenceCorrelation_inversion {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (d : ZMod N) :
    mixedDifferenceCorrelation A B d = (N : Complex)⁻¹ *
      ∑ r : ZMod N, (mixedFourierWeight A B r : Complex) * exponential (r * d) := by
  rw [identity_2_4_holds N (mixedDifferenceCorrelation A B) d]
  simp only [fourier_mixedDifferenceCorrelation]

/-- A nonzero mixed correlation gives an actual sum of differences. -/
theorem mixedDifferenceCorrelation_representation {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (d : ZMod N) (hne : mixedDifferenceCorrelation A B d ≠ 0) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B, d = (a₁ - a₂) + (b₁ - b₂) := by
  unfold mixedDifferenceCorrelation correlation at hne
  obtain ⟨t, ht, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hleft : (∑ x : ZMod N, indicator A x * star (indicator A (x - t))) ≠ 0 := by
    intro h
    simp only [h, zero_mul, ne_eq, not_true_eq_false] at hprod
  have hright : (∑ y : ZMod N, indicator B y * star (indicator B (y - (t - d)))) ≠ 0 := by
    intro h
    simp only [h, star_zero, mul_zero, ne_eq, not_true_eq_false] at hprod
  obtain ⟨x, hx, hxprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hleft
  obtain ⟨y, hy, hyprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hright
  have hxA : x ∈ A := by by_contra h; simp [indicator, h] at hxprod
  have hxtA : x - t ∈ A := by by_contra h; simp [indicator, h] at hxprod
  have hyB : y ∈ B := by by_contra h; simp [indicator, h] at hyprod
  have hydB : y - (t - d) ∈ B := by by_contra h; simp [indicator, h] at hyprod
  exact ⟨x, hxA, x - t, hxtA, y - (t - d), hydB, y, hyB, by ring⟩

/-- The total nonnegative Fourier weight equals N times the correlation at zero. -/
theorem mixedDifferenceCorrelation_zero_norm {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) :
    ‖mixedDifferenceCorrelation A B 0‖ = (N : Real)⁻¹ * ∑ r, mixedFourierWeight A B r := by
  have heq : mixedDifferenceCorrelation A B 0 =
      (((N : Real)⁻¹ * ∑ r, mixedFourierWeight A B r : Real) : Complex) := by
    rw [mixedDifferenceCorrelation_inversion]
    simp [exponential, Complex.ofReal_sum]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => mixedFourierWeight_nonneg A B r)

/-- The zero frequency supplies the density lower bound. -/
theorem mixedDifferenceCorrelation_zero_lower {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) :
    (A.card : Real)^2 * (B.card : Real)^2 / N ≤ ‖mixedDifferenceCorrelation A B 0‖ := by
  have hzero (C : Finset (ZMod N)) : fourier (indicator C) 0 = (C.card : Complex) := by
    simp [fourier, ZMod.dft_apply, indicator]
  have hw : mixedFourierWeight A B 0 = (A.card : Real)^2 * (B.card : Real)^2 := by
    simp only [mixedFourierWeight, hzero, Complex.norm_natCast]
  rw [mixedDifferenceCorrelation_zero_norm, div_eq_inv_mul, ← hw]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun r _ => mixedFourierWeight_nonneg A B r) (Finset.mem_univ 0))
    (by positivity)

/-- The Fourier weighted phase error controls displacement from zero. -/
theorem mixedDifferenceCorrelation_shift_bound {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (d : ZMod N) :
    ‖mixedDifferenceCorrelation A B d - mixedDifferenceCorrelation A B 0‖ ≤
      (N : Real)⁻¹ * ∑ r, mixedFourierWeight A B r * ‖exponential (r * d) - 1‖ := by
  have heq : mixedDifferenceCorrelation A B d - mixedDifferenceCorrelation A B 0 =
      (N : Complex)⁻¹ * ∑ r, (mixedFourierWeight A B r : Complex) * (exponential (r * d) - 1) := by
    rw [mixedDifferenceCorrelation_inversion, mixedDifferenceCorrelation_inversion,
      ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    simp only [mul_zero, exponential, AddChar.map_zero_eq_one]
    ring
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mixedFourierWeight_nonneg A B r)]

end LeanProofs.GowersSzemeredi
