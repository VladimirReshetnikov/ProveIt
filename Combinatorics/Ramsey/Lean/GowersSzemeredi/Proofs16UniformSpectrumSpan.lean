import GowersSzemeredi.Proofs16BohrSumSpan

/-! Remove the finite-size restriction from polynomial spectrum inclusion.
For small prime moduli the polynomial cutoff covers all coefficients;
a nonzero defining frequency then spans the entire group. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The zero combination belongs to every bounded frequency span. -/
theorem zero_mem_boundedFrequencySpan {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (gamma : ι → ZMod N) (R : Nat) : (0 : ZMod N) ∈ boundedFrequencySpan gamma R := by
  let v : ι → centeredBall N R := fun _ => ⟨0, by simp [centeredBall, centeredAbs]⟩
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, by simp [v]⟩

/-- A full coefficient interval and one nonzero frequency span a prime field. -/
theorem boundedFrequencySpan_eq_univ {N : Nat} [NeZero N] [Fact N.Prime]
    {ι : Type*} [Fintype ι] (gamma : ι → ZMod N) (i : ι) (hi : gamma i ≠ 0)
    {R : Nat} (hR : N / 2 ≤ R) : boundedFrequencySpan gamma R = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  have hball (z : ZMod N) : z ∈ centeredBall N R := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ZMod.natAbs_valMinAbs_le z).trans hR⟩
  let v : ι → centeredBall N R := fun j => ⟨if j = i then x / gamma i else 0, hball _⟩
  refine Finset.mem_image.mpr ⟨v, Finset.mem_univ _, ?_⟩
  change (∑ j, (if j = i then x / gamma i else 0) * gamma j) = x
  simp [ite_mul, hi]

/-- With only zero frequencies, the Bohr set is the entire group. -/
theorem bohr_eq_univ_of_zero_frequencies {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (hK : ∀ r ∈ K, r = 0) {rho : Real} (hrho : 0 ≤ rho) :
    bohr K rho = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  rw [hK r hr]
  simp only [zero_mul, centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero]
  positivity

/-- The full-group indicator has no nonzero Fourier coefficient. -/
theorem fourier_univ_eq_zero {N : Nat} [NeZero N] {xi : ZMod N} (hxi : xi ≠ 0) :
    fourier (indicator (Finset.univ : Finset (ZMod N))) xi = 0 := by
  unfold fourier
  rw [ZMod.dft_apply]
  simp only [indicator, Finset.mem_univ, if_true, smul_eq_mul, mul_one]
  have h := AddChar.sum_mulShift (-xi) (ZMod.isPrimitive_stdAddChar N)
  rw [if_neg (neg_ne_zero.mpr hxi)] at h
  simpa only [mul_neg, Nat.cast_zero] using h

/-- The polynomial cutoff dominates the small-modulus threshold. -/
theorem polynomialSpectrumCutoff_ge_threshold (m : Nat) (rho : Real) {epsilon : Real}
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1) :
    8 * (m + 1 : Real) / epsilon ≤ (polynomialSpectrumCutoff m rho epsilon : Real) := by
  let q : Real := (m + 1 : Real) / epsilon
  have hq : 1 ≤ q := (le_div_iff₀ heps).mpr (by have := Nat.cast_nonneg (α := Real) m; linarith)
  have hquad : 8 * q ≤ 128 * q^2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have heq : 128 * q^2 = 128 * (m + 1 : Real)^2 / epsilon^2 := by dsimp [q]; ring
  rw [heq] at hquad
  have hceil := Nat.le_ceil (max (8 * (m + 1 : Real) / (epsilon * rho))
    (128 * (m + 1 : Real)^2 / epsilon^2))
  change _ ≤ (polynomialSpectrumCutoff m rho epsilon : Real) at hceil
  have hmax := le_max_right (8 * (m + 1 : Real) / (epsilon * rho))
    (128 * (m + 1 : Real)^2 / epsilon^2)
  dsimp [q] at hquad
  rw [← mul_div_assoc] at hquad
  exact hquad.trans (hmax.trans hceil)

/-- Polynomial large-spectrum inclusion for every prime modulus. -/
theorem large_bohr_fourier_mem_uniform_boundedSpan {N : Nat} [NeZero N] [Fact N.Prime]
    (K : Finset (ZMod N)) {rho epsilon : Real}
    (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    {xi : ZMod N} (hlarge : epsilon * N ≤ ‖fourier (indicator (bohr K rho)) xi‖) :
    xi ∈ boundedFrequencySpan (fun gamma : K => (gamma : ZMod N))
      (polynomialSpectrumCutoff K.card rho epsilon) := by
  by_cases hN : 8 * (K.card + 1 : Real) / epsilon ≤ (N : Real)
  · exact large_bohr_fourier_mem_polynomial_boundedSpan K hrho hrhoHalf heps heps1 hN hlarge
  · by_cases hK : ∃ r ∈ K, r ≠ 0
    · obtain ⟨r, hr, hr0⟩ := hK
      have hbound := polynomialSpectrumCutoff_ge_threshold K.card rho heps heps1
      have hNR : (N : Real) ≤ polynomialSpectrumCutoff K.card rho epsilon := by linarith
      have hRN : N ≤ polynomialSpectrumCutoff K.card rho epsilon := by exact_mod_cast hNR
      have hfull := boundedFrequencySpan_eq_univ (fun gamma : K => (gamma : ZMod N)) ⟨r, hr⟩ hr0
        ((Nat.div_le_self N 2).trans hRN)
      rw [hfull]
      exact Finset.mem_univ _
    · have hzfreq : ∀ r ∈ K, r = 0 := by simpa only [not_exists, not_and, not_not] using hK
      have hfull := bohr_eq_univ_of_zero_frequencies K hzfreq hrho.le
      have hxi : xi = 0 := by
        by_contra hxi
        rw [hfull, fourier_univ_eq_zero hxi, norm_zero] at hlarge
        have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
        have := mul_pos heps hNR
        linarith
      rw [hxi]
      exact zero_mem_boundedFrequencySpan _ _

/-- Bohr-sum containment without a lower bound on the modulus. -/
theorem bohr_sum_contains_span_intersection_uniform {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) {rho sigma : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (d : ZMod N)
    (hd : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N))
        (polynomialSpectrumCutoff K.card (rho / 2) (bohrSumThreshold K L rho sigma)) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N))
        (polynomialSpectrumCutoff L.card (sigma / 2) (bohrSumThreshold K L rho sigma)))
      (1 / (4 * Real.pi))) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L sigma, d = x + y := by
  obtain ⟨htau, htau1⟩ := bohrSumThreshold_bounds K L hrho.le hsigma.le
  apply bohr_sum_of_common_spectrum K L hrho.le hsigma.le d
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  have hlarge := (Finset.mem_filter.mp hr).2
  have hK := large_bohr_fourier_mem_uniform_boundedSpan K (half_pos hrho)
    (by linarith : rho / 2 < 1 / 2) htau htau1 hlarge.1
  have hL := large_bohr_fourier_mem_uniform_boundedSpan L (half_pos hsigma)
    (by linarith : sigma / 2 < 1 / 2) htau htau1 hlarge.2
  exact (Finset.mem_filter.mp hd).2 r (Finset.mem_inter.mpr ⟨hK, hL⟩)

end LeanProofs.GowersSzemeredi
