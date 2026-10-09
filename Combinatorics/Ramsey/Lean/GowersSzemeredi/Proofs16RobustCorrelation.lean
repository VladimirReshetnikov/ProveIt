import GowersSzemeredi.Proofs16MixedBogolyubov

/-! Quantitative mixed-correlation bounds, retaining the number of witnesses
rather than only their existence. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A phase bound on a spectrum gives a lower bound on the correlation
at every controlled displacement, with an explicit exceptional-mass loss. -/
theorem mixed_correlation_lower_of_phase_tail {N : Nat} [NeZero N]
    (A B S : Finset (ZMod N)) (d : ZMod N)
    (hphase : ∀ r ∈ S, ‖exponential (r * d) - 1‖ ≤ 1 / 2) :
    (A.card : Real)^2 * (B.card : Real)^2 / (2 * N) -
      2 * (∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r) / N ≤
        ‖mixedDifferenceCorrelation A B d‖ := by
  have hshift := (mixedDifferenceCorrelation_shift_bound A B d).trans
    (mul_le_mul_of_nonneg_left (mixed_weighted_phase_le A B S d hphase) (by positivity))
  have heq : (N : Real)⁻¹ * ((1 / 2 : Real) * ∑ r, mixedFourierWeight A B r +
      2 * ∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r) =
      (1 / 2 : Real) * ‖mixedDifferenceCorrelation A B 0‖ +
        2 * (∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r) / N := by
    rw [mixedDifferenceCorrelation_zero_norm]
    ring
  rw [heq] at hshift
  have htri := norm_sub_norm_le (mixedDifferenceCorrelation A B 0)
    (mixedDifferenceCorrelation A B d)
  rw [norm_sub_rev] at htri
  have hzero := mixedDifferenceCorrelation_zero_lower A B
  have heq' : (A.card : Real)^2 * (B.card : Real)^2 / (2 * N) =
      (1 / 2 : Real) * ((A.card : Real)^2 * (B.card : Real)^2 / N) := by ring
  rw [heq']
  linarith

/-- The intersection spectrum has the usual Parseval rank bound. -/
theorem commonLargeSpectrum_card_le {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) {tau : Real} (htau : 0 < tau) :
    ((commonLargeSpectrum A B tau).card : Real) ≤
      (A.card : Real) / (tau^2 * N) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hsum : ((commonLargeSpectrum A B tau).card : Real) * (tau * N)^2 ≤
      N * (A.card : Real) := by
    calc
      _ = ∑ r ∈ commonLargeSpectrum A B tau, (tau * N)^2 := by simp
      _ ≤ ∑ r ∈ commonLargeSpectrum A B tau, ‖fourier (indicator A) r‖^2 := by
        apply Finset.sum_le_sum
        intro r hr
        have h := (Finset.mem_filter.mp hr).2.1
        exact pow_le_pow_left₀ (by positivity) h 2
      _ ≤ ∑ r : ZMod N, ‖fourier (indicator A) r‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
      _ = _ := indicator_fourier_energy A
  apply (le_div_iff₀ (by positivity : 0 < tau^2 * (N : Real))).mpr
  have := (mul_le_mul_iff_right₀ hN).mp (show
      (N : Real) * (((commonLargeSpectrum A B tau).card : Real) * (tau^2 * N)) ≤
        N * (A.card : Real) by nlinarith only [hsum])
  exact this

/-- At density alpha, a rank at most 16/alpha² spectrum controls at least
alpha⁴ N³/4 representations. This is a correlation bound; the conversion
to an actual finite count is supplied separately. -/
theorem robust_self_correlation {N : Nat} [NeZero N]
    (W : Finset (ZMod N)) {alpha : Real} (ha : 0 < alpha)
    (hcard : (W.card : Real) = alpha * N) :
    let S := commonLargeSpectrum W W (Real.sqrt (alpha^3) / 4)
    (S.card : Real) ≤ 16 / alpha^2 ∧
      ∀ d ∈ bohr S (1 / (4 * Real.pi)),
        alpha^4 * (N : Real)^3 / 4 ≤ ‖mixedDifferenceCorrelation W W d‖ := by
  dsimp only
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hs : 0 < Real.sqrt (alpha^3) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ alpha^3 by positivity)
  let tau := Real.sqrt (alpha^3) / 4
  have htau : 0 < tau := by dsimp [tau]; positivity
  have htau2 : tau^2 = alpha^3 / 16 := by dsimp [tau]; nlinarith only [hs2]
  constructor
  · have h := commonLargeSpectrum_card_le W W htau
    rw [hcard, htau2] at h
    have heq : alpha * (N : Real) / (alpha^3 / 16 * N) = 16 / alpha^2 := by
      field_simp
    simpa only [heq] using h
  · intro d hd
    have hphase : ∀ r ∈ commonLargeSpectrum W W tau,
        ‖exponential (r * d) - 1‖ ≤ 1 / 2 := by
      intro r hr
      have hc := (Finset.mem_filter.mp hd).2 r hr
      have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * Real.pi by positivity)
      have heq : 2 * Real.pi * ((1 / (4 * Real.pi)) * (N : Real)) =
          (1 / 2 : Real) * N := by field_simp; ring
      apply (downstream_norm_exponential_sub_one_le (r * d)).trans
      apply (div_le_iff₀ hN).mpr
      linarith only [h, heq]
    have hlower := mixed_correlation_lower_of_phase_tail W W
      (commonLargeSpectrum W W tau) d hphase
    have htail := mixedFourierWeight_tail_le W W htau.le
    rw [htau2, hcard] at htail
    have htail' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left htail (show (0 : Real) ≤ 2 by norm_num)) hN.le
    have heq : 2 * (alpha^3 / 16 * (N : Real)^3 * (alpha * N + alpha * N)) / N =
        alpha^4 * (N : Real)^3 / 4 := by field_simp; ring
    rw [heq] at htail'
    rw [hcard] at hlower
    have heq' : (alpha * (N : Real))^2 * (alpha * N)^2 / (2 * N) =
        alpha^4 * (N : Real)^3 / 2 := by field_simp
    rw [heq'] at hlower
    linarith

end LeanProofs.GowersSzemeredi
