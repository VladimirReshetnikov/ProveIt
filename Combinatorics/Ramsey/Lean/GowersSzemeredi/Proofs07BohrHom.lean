import GowersSzemeredi.Proofs01_03
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Bogolyubov--Freiman homomorphism lemma

This module proves Gowers's Lemma 7.8.  The analytic part truncates the
Fourier inversion formula for the fourfold difference count to the large
spectrum.  The algebraic part uses the order-eight Freiman hypothesis to
make the induced map on `2A-2A` well defined and additive.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma lemma78_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma lemma78_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

@[simp] private lemma lemma78_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact (ZMod.stdAddChar (N := N)).norm_apply x

@[simp] private lemma lemma78_indicator_star {N : Nat}
    (A : Finset (ZMod N)) (x : ZMod N) : star (indicator A x) = indicator A x := by
  classical
  by_cases hx : x ∈ A <;> simp [indicator, hx]

private lemma lemma78_fourier_indicator_zero {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : fourier (indicator A) 0 = (A.card : Complex) := by
  classical
  simp [fourier, ZMod.dft_apply, indicator]

private lemma lemma78_fourier_indicator_norm_le_card {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) :
    ‖fourier (indicator A) r‖ <= A.card := by
  classical
  rw [fourier, ZMod.dft_apply]
  calc
    ‖∑ x : ZMod N, ZMod.stdAddChar (-(x * r)) • indicator A x‖ <=
        ∑ x : ZMod N, ‖ZMod.stdAddChar (-(x * r)) • indicator A x‖ :=
      norm_sum_le _ _
    _ = ∑ x : ZMod N, if x ∈ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [indicator, hx]
    _ = A.card := by simp

private lemma lemma78_fourier_indicator_energy {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2) =
      (N : Real) * A.card := by
  rw [identity_2_3_holds]
  congr 1
  classical
  calc
    (∑ x : ZMod N, ‖indicator A x‖ ^ 2) =
        ∑ x : ZMod N, if x ∈ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [indicator, hx]
    _ = A.card := by simp

private lemma lemma78_spectrum_card_bound {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) :
    ((section7Spectrum A alpha).card : Real) <= 16 * alpha ^ (-(2 : Real)) := by
  let lambda : Real := alpha ^ ((3 : Real) / 2) / 4
  have hlambda : 0 < lambda := by positivity
  have hspectrum (r : ZMod N) (hr : r ∈ section7Spectrum A alpha) :
      lambda * N <= ‖fourier (indicator A) r‖ := by
    rw [section7Spectrum, largeFourierSpectrum, Finset.mem_filter] at hr
    dsimp [lambda]
    convert hr.2 using 1
    ring
  have hsumLower :
      ((section7Spectrum A alpha).card : Real) * (lambda * N) ^ 2 <=
        ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2 := by
    calc
      ((section7Spectrum A alpha).card : Real) * (lambda * N) ^ 2 =
          ∑ _r ∈ section7Spectrum A alpha, (lambda * N) ^ 2 := by simp
      _ <= ∑ r ∈ section7Spectrum A alpha,
          ‖fourier (indicator A) r‖ ^ 2 := by
        gcongr with r hr
        exact hspectrum r hr
      _ <= ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
  rw [lemma78_fourier_indicator_energy, hcard] at hsumLower
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcalc : lambda ^ 2 = alpha ^ 3 / 16 := by
    dsimp [lambda]
    rw [div_pow]
    have hpow : (alpha ^ ((3 : Real) / 2)) ^ (2 : Nat) = alpha ^ 3 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul halpha.le]
      norm_num
    rw [hpow]
    norm_num
  have hscaled :
      (((section7Spectrum A alpha).card : Real) * lambda ^ 2) * (N : Real) ^ 2 <=
        alpha * (N : Real) ^ 2 := by
    calc
      (((section7Spectrum A alpha).card : Real) * lambda ^ 2) * (N : Real) ^ 2 =
          ((section7Spectrum A alpha).card : Real) * (lambda * N) ^ 2 := by ring
      _ <= (N : Real) * (alpha * N) := hsumLower
      _ = alpha * (N : Real) ^ 2 := by ring
  have hcancel : ((section7Spectrum A alpha).card : Real) * lambda ^ 2 <= alpha := by
    exact le_of_mul_le_mul_right hscaled (sq_pos_of_pos hN)
  have hraw : ((section7Spectrum A alpha).card : Real) <= alpha / lambda ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hlambda)).2 hcancel
  calc
    ((section7Spectrum A alpha).card : Real) <= alpha / lambda ^ 2 := hraw
    _ = 16 * alpha ^ (-(2 : Real)) := by
      rw [hcalc]
      calc
        alpha / (alpha ^ 3 / 16) = 16 / alpha ^ 2 := by
          field_simp [ne_of_gt halpha]
        _ = 16 * alpha ^ (-(2 : Real)) := by
          rw [Real.rpow_neg halpha.le]
          norm_num [Real.rpow_two, div_eq_mul_inv]

private def lemma78PairCorrelation {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : ZMod N -> Complex :=
  correlation (indicator A) (indicator A)

private def lemma78FourCorrelation {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : ZMod N -> Complex :=
  correlation (lemma78PairCorrelation A) (lemma78PairCorrelation A)

private lemma lemma78_fourier_pairCorrelation {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) :
    fourier (lemma78PairCorrelation A) r =
      ((‖fourier (indicator A) r‖ ^ 2 : Real) : Complex) := by
  rw [lemma78PairCorrelation, identity_2_1_holds]
  rw [Complex.star_def, Complex.mul_conj']
  norm_cast

private lemma lemma78_fourier_fourCorrelation {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) :
    fourier (lemma78FourCorrelation A) r =
      ((‖fourier (indicator A) r‖ ^ 4 : Real) : Complex) := by
  rw [lemma78FourCorrelation, identity_2_1_holds,
    lemma78_fourier_pairCorrelation, Complex.star_def, Complex.conj_ofReal]
  norm_cast
  ring

private lemma lemma78_fourCorrelation_inversion {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (d : ZMod N) :
    lemma78FourCorrelation A d = (N : Complex)⁻¹ *
      ∑ r : ZMod N,
        ((‖fourier (indicator A) r‖ ^ 4 : Real) : Complex) * exponential (r * d) := by
  rw [identity_2_4_holds N (lemma78FourCorrelation A) d]
  apply congrArg ((N : Complex)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro r _
  rw [lemma78_fourier_fourCorrelation]

private lemma lemma78_exponential_eq_exp_valMinAbs {N : Nat} [NeZero N]
    (x : ZMod N) :
    exponential x =
      Complex.exp (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
  calc
    exponential x = ZMod.stdAddChar ((x.valMinAbs : Int) : ZMod N) := by
      simp [exponential]
    _ = Complex.exp (2 * Real.pi * Complex.I * (x.valMinAbs : Int) / N) :=
      ZMod.stdAddChar_coe x.valMinAbs
    _ = Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
      congr 1
      push_cast
      ring

private lemma lemma78_norm_exponential_sub_one_le {N : Nat} [NeZero N]
    (x : ZMod N) :
    ‖exponential x - 1‖ <= 2 * Real.pi * centeredAbs x / N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have habsval : |(x.valMinAbs : Real)| = (centeredAbs x : Real) := by
    rw [centeredAbs, ← Int.cast_abs, Int.abs_eq_natAbs]
    rfl
  rw [lemma78_exponential_eq_exp_valMinAbs]
  calc
    ‖Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) - 1‖ <=
        ‖2 * Real.pi * (x.valMinAbs : Real) / N‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * centeredAbs x / N := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) <= 2),
        abs_of_pos Real.pi_pos, habsval, abs_of_pos hN]

private lemma lemma78_bohr_phase_bound {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi)))
    (r : ZMod N) (hr : r ∈ section7Spectrum A alpha) :
    ‖exponential (r * d) - 1‖ <= alpha / 16 := by
  rw [bohr, Finset.mem_filter] at hd
  have hcenter := hd.2 r hr
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hpi : (0 : Real) < Real.pi := Real.pi_pos
  calc
    ‖exponential (r * d) - 1‖ <=
        2 * Real.pi * centeredAbs (r * d) / N :=
      lemma78_norm_exponential_sub_one_le (r * d)
    _ <= alpha / 16 := by
      apply (div_le_iff₀ hN).2
      calc
        2 * Real.pi * (centeredAbs (r * d) : Real) <=
            2 * Real.pi * ((alpha / (32 * Real.pi)) * N) := by
          gcongr
        _ = (alpha / 16) * N := by field_simp [Real.pi_ne_zero]; ring

private lemma lemma78_norm_exponential_sub_one_le_two {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x - 1‖ <= 2 := by
  calc
    ‖exponential x - 1‖ <= ‖exponential x‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [lemma78_norm_exponential]

private lemma lemma78_alpha_le_one {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real)
    (hcard : (A.card : Real) = alpha * N) : alpha <= 1 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcardN : (A.card : Real) <= N := by
    exact_mod_cast (by simpa only [ZMod.card] using A.card_le_univ)
  rw [hcard] at hcardN
  nlinarith

private lemma lemma78_fourth_moment_upper {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real)
    (hcard : (A.card : Real) = alpha * N) :
    (∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4) <=
      alpha ^ 3 * (N : Real) ^ 4 := by
  have hsum :
      (∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4) <=
        (A.card : Real) ^ 2 *
          ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2 := by
    calc
      (∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4) =
          ∑ r : ZMod N,
            ‖fourier (indicator A) r‖ ^ 2 *
              ‖fourier (indicator A) r‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ <= ∑ r : ZMod N,
          (A.card : Real) ^ 2 * ‖fourier (indicator A) r‖ ^ 2 := by
        gcongr with r
        exact lemma78_fourier_indicator_norm_le_card A r
      _ = (A.card : Real) ^ 2 *
          ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2 := by
        rw [Finset.mul_sum]
  rw [lemma78_fourier_indicator_energy] at hsum
  calc
    (∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4) <=
        (A.card : Real) ^ 2 * ((N : Real) * A.card) := hsum
    _ = alpha ^ 3 * (N : Real) ^ 4 := by rw [hcard]; ring

private lemma lemma78_small_spectrum_tail {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha lambda : Real)
    (hlambda : lambda = alpha ^ ((3 : Real) / 2) / 4)
    (hcard : (A.card : Real) = alpha * N) :
    (∑ r ∈ (Finset.univ.filter fun r : ZMod N =>
        r ∉ section7Spectrum A alpha), ‖fourier (indicator A) r‖ ^ 4) <=
      alpha * lambda ^ 2 * (N : Real) ^ 4 := by
  have hterm (r : ZMod N) (hr : r ∉ section7Spectrum A alpha) :
      ‖fourier (indicator A) r‖ ^ 4 <=
        (lambda * N) ^ 2 * ‖fourier (indicator A) r‖ ^ 2 := by
    have hrlt : ‖fourier (indicator A) r‖ < lambda * N := by
      rw [section7Spectrum, largeFourierSpectrum, Finset.mem_filter] at hr
      simp only [Finset.mem_univ, true_and, not_le] at hr
      rw [hlambda]
      simpa only [div_mul_eq_mul_div] using hr
    calc
      ‖fourier (indicator A) r‖ ^ 4 =
          ‖fourier (indicator A) r‖ ^ 2 *
            ‖fourier (indicator A) r‖ ^ 2 := by ring
      _ <= (lambda * N) ^ 2 * ‖fourier (indicator A) r‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hrlt.le 2) (sq_nonneg _)
  calc
    (∑ r ∈ (Finset.univ.filter fun r : ZMod N =>
        r ∉ section7Spectrum A alpha), ‖fourier (indicator A) r‖ ^ 4) <=
        ∑ r ∈ (Finset.univ.filter fun r : ZMod N =>
          r ∉ section7Spectrum A alpha),
          (lambda * N) ^ 2 * ‖fourier (indicator A) r‖ ^ 2 := by
      gcongr with r hr
      exact hterm r (Finset.mem_filter.mp hr).2
    _ = (lambda * N) ^ 2 *
        ∑ r ∈ (Finset.univ.filter fun r : ZMod N =>
          r ∉ section7Spectrum A alpha),
          ‖fourier (indicator A) r‖ ^ 2 := by rw [Finset.mul_sum]
    _ <= (lambda * N) ^ 2 *
        ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
      · positivity
    _ = alpha * lambda ^ 2 * (N : Real) ^ 4 := by
      rw [lemma78_fourier_indicator_energy, hcard]
      ring

private lemma lemma78_lambda_sq (alpha lambda : Real) (halpha : 0 < alpha)
    (hlambda : lambda = alpha ^ ((3 : Real) / 2) / 4) :
    lambda ^ 2 = alpha ^ 3 / 16 := by
  rw [hlambda, div_pow]
  have hpow : (alpha ^ ((3 : Real) / 2)) ^ (2 : Nat) = alpha ^ 3 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul halpha.le]
    norm_num
  rw [hpow]
  norm_num

private lemma lemma78_weighted_phase_sum {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha lambda : Real) (halpha : 0 < alpha)
    (hlambda : lambda = alpha ^ ((3 : Real) / 2) / 4)
    (hcard : (A.card : Real) = alpha * N) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi))) :
    (∑ r : ZMod N,
        ‖fourier (indicator A) r‖ ^ 4 * ‖exponential (r * d) - 1‖) <=
      3 * alpha * lambda ^ 2 * (N : Real) ^ 4 := by
  let K := section7Spectrum A alpha
  let w : ZMod N -> Real := fun r =>
    ‖fourier (indicator A) r‖ ^ 4 * ‖exponential (r * d) - 1‖
  let F : ZMod N -> Real := fun r => ‖fourier (indicator A) r‖ ^ 4
  have hmain :
      ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∈ K), w r <=
        (alpha / 16) * ∑ r : ZMod N, F r := by
    calc
      ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∈ K), w r <=
          ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∈ K),
            (alpha / 16) * F r := by
        gcongr with r hr
        dsimp [w, F]
        rw [mul_comm (alpha / 16)]
        apply mul_le_mul_of_nonneg_left
        · exact lemma78_bohr_phase_bound A alpha d hd r
            (by simpa [K] using (Finset.mem_filter.mp hr).2)
        · positivity
      _ = (alpha / 16) *
          ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∈ K), F r := by
        rw [Finset.mul_sum]
      _ <= (alpha / 16) * ∑ r : ZMod N, F r := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
        · positivity
  have htailPhase :
      ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∉ K), w r <=
        2 * ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∉ K), F r := by
    calc
      ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∉ K), w r <=
          ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∉ K), 2 * F r := by
        gcongr with r hr
        dsimp [w, F]
        nlinarith [lemma78_norm_exponential_sub_one_le_two (r * d),
          pow_nonneg (norm_nonneg (fourier (indicator A) r)) 4]
      _ = 2 * ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∉ K), F r := by
        rw [Finset.mul_sum]
  have htotal := lemma78_fourth_moment_upper A alpha hcard
  have htail := lemma78_small_spectrum_tail A alpha lambda hlambda hcard
  have hsplit :
      (∑ r : ZMod N, w r) =
        (∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∈ K), w r) +
          ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∉ K), w r := by
    simpa only [Finset.mem_univ, true_and] using
      (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod N))
        (fun r => r ∈ K) w).symm
  rw [show (∑ r : ZMod N,
      ‖fourier (indicator A) r‖ ^ 4 * ‖exponential (r * d) - 1‖) =
      ∑ r : ZMod N, w r by rfl, hsplit]
  calc
    (∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∈ K), w r) +
        ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∉ K), w r <=
        (alpha / 16) * ∑ r : ZMod N, F r +
          2 * ∑ r ∈ (Finset.univ.filter fun r : ZMod N => r ∉ K), F r :=
      add_le_add hmain htailPhase
    _ <= (alpha / 16) * (alpha ^ 3 * (N : Real) ^ 4) +
          2 * (alpha * lambda ^ 2 * (N : Real) ^ 4) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left
        · simpa [F] using htotal
        · positivity
      · apply mul_le_mul_of_nonneg_left
        · simpa [F, K] using htail
        · norm_num
    _ = 3 * alpha * lambda ^ 2 * (N : Real) ^ 4 := by
      rw [lemma78_lambda_sq alpha lambda halpha hlambda]
      ring

private lemma lemma78_fourCorrelation_sub_zero {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (d : ZMod N) :
    lemma78FourCorrelation A d - lemma78FourCorrelation A 0 =
      (N : Complex)⁻¹ * ∑ r : ZMod N,
        ((‖fourier (indicator A) r‖ ^ 4 : Real) : Complex) *
          (exponential (r * d) - 1) := by
  rw [lemma78_fourCorrelation_inversion A d,
    lemma78_fourCorrelation_inversion A 0]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  apply congrArg ((N : Complex)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro r _
  simp only [mul_zero]
  have hzero : exponential (0 : ZMod N) = 1 := by
    exact AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))
  rw [hzero]
  ring

private lemma lemma78_fourCorrelation_shift_bound {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha lambda : Real) (halpha : 0 < alpha)
    (hlambda : lambda = alpha ^ ((3 : Real) / 2) / 4)
    (hcard : (A.card : Real) = alpha * N) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi))) :
    ‖lemma78FourCorrelation A d - lemma78FourCorrelation A 0‖ <=
      3 * alpha * lambda ^ 2 * (N : Real) ^ 3 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  rw [lemma78_fourCorrelation_sub_zero]
  calc
    ‖(N : Complex)⁻¹ * ∑ r : ZMod N,
        ((‖fourier (indicator A) r‖ ^ 4 : Real) : Complex) *
          (exponential (r * d) - 1)‖ =
        (N : Real)⁻¹ * ‖∑ r : ZMod N,
          ((‖fourier (indicator A) r‖ ^ 4 : Real) : Complex) *
            (exponential (r * d) - 1)‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ <= (N : Real)⁻¹ * ∑ r : ZMod N,
        ‖((‖fourier (indicator A) r‖ ^ 4 : Real) : Complex) *
          (exponential (r * d) - 1)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = (N : Real)⁻¹ * ∑ r : ZMod N,
        ‖fourier (indicator A) r‖ ^ 4 * ‖exponential (r * d) - 1‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    _ <= (N : Real)⁻¹ *
        (3 * alpha * lambda ^ 2 * (N : Real) ^ 4) := by
      gcongr
      exact lemma78_weighted_phase_sum A alpha lambda halpha hlambda hcard d hd
    _ = 3 * alpha * lambda ^ 2 * (N : Real) ^ 3 := by
      field_simp [ne_of_gt hN]

private lemma lemma78_fourCorrelation_zero_lower {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha lambda : Real) (halpha : 0 < alpha)
    (hlambda : lambda = alpha ^ ((3 : Real) / 2) / 4)
    (hcard : (A.card : Real) = alpha * N) :
    4 * alpha * lambda ^ 2 * (N : Real) ^ 3 <=
      ‖lemma78FourCorrelation A 0‖ := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hsumNonneg :
      0 <= ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4 := by positivity
  have hzeroTerm :
      (A.card : Real) ^ 4 <=
        ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4 := by
    have hmem : (0 : ZMod N) ∈ (Finset.univ : Finset (ZMod N)) := Finset.mem_univ _
    have hsingle := Finset.single_le_sum
      (fun r (_hr : r ∈ (Finset.univ : Finset (ZMod N))) =>
        pow_nonneg (norm_nonneg (fourier (indicator A) r)) 4) hmem
    simpa [lemma78_fourier_indicator_zero] using hsingle
  rw [lemma78_fourCorrelation_inversion A 0]
  have hzero : exponential (0 : ZMod N) = 1 :=
    AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))
  simp only [mul_zero, hzero, mul_one]
  rw [← Complex.ofReal_sum, norm_mul, norm_inv, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsumNonneg]
  have hlambdaSq := lemma78_lambda_sq alpha lambda halpha hlambda
  have hmain :
      4 * alpha * lambda ^ 2 * (N : Real) ^ 3 <=
        (N : Real)⁻¹ * (A.card : Real) ^ 4 := by
    rw [hlambdaSq, hcard]
    field_simp [ne_of_gt hN]
    nlinarith [sq_nonneg (alpha ^ 2 * (N : Real) ^ 2)]
  exact hmain.trans (mul_le_mul_of_nonneg_left hzeroTerm (by positivity))

private lemma lemma78_fourCorrelation_ne_zero_of_mem_bohr {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi))) :
    lemma78FourCorrelation A d != 0 := by
  let lambda : Real := alpha ^ ((3 : Real) / 2) / 4
  have hlambda : lambda = alpha ^ ((3 : Real) / 2) / 4 := rfl
  have hpositive : 0 < alpha * lambda ^ 2 * (N : Real) ^ 3 := by
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    positivity
  have hshift :=
    lemma78_fourCorrelation_shift_bound A alpha lambda halpha hlambda hcard d hd
  have hzero := lemma78_fourCorrelation_zero_lower A alpha lambda halpha hlambda hcard
  have hlt :
      ‖lemma78FourCorrelation A d - lemma78FourCorrelation A 0‖ <
        ‖lemma78FourCorrelation A 0‖ := by
    nlinarith
  rw [bne_iff_ne]
  intro hd0
  rw [hd0, zero_sub, norm_neg] at hlt
  exact (lt_irrefl _ hlt)

private structure Lemma78Representation {N : Nat}
    (A : Finset (ZMod N)) (d : ZMod N) where
  a : ZMod N
  b : ZMod N
  c : ZMod N
  e : ZMod N
  ha : a ∈ A
  hb : b ∈ A
  hc : c ∈ A
  he : e ∈ A
  relation : a + e - b - c = d

private def Lemma78Representation.value {N : Nat}
    {A : Finset (ZMod N)} {d : ZMod N}
    (phi : ZMod N -> ZMod N) (q : Lemma78Representation A d) : ZMod N :=
  phi q.a + phi q.e - phi q.b - phi q.c

private lemma lemma78_pairCorrelation_star {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (t : ZMod N) :
    star (lemma78PairCorrelation A t) = lemma78PairCorrelation A t := by
  classical
  unfold lemma78PairCorrelation correlation
  simp only [star_sum, star_mul, lemma78_indicator_star]
  apply Finset.sum_congr rfl
  intro x _
  ring

private lemma lemma78_representation_of_fourCorrelation_ne_zero
    {N : Nat} [NeZero N] (A : Finset (ZMod N)) (d : ZMod N)
    (hne : lemma78FourCorrelation A d != 0) :
    Nonempty (Lemma78Representation A d) := by
  classical
  rw [bne_iff_ne] at hne
  unfold lemma78FourCorrelation correlation at hne
  obtain ⟨t, _htmem, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [lemma78_pairCorrelation_star] at ht
  have hleft : lemma78PairCorrelation A t != 0 := by
    rw [bne_iff_ne]
    intro hzero
    simp [hzero] at ht
  have hright : lemma78PairCorrelation A (t - d) != 0 := by
    rw [bne_iff_ne]
    intro hzero
    simp [hzero] at ht
  rw [bne_iff_ne] at hleft hright
  unfold lemma78PairCorrelation correlation at hleft hright
  simp only [lemma78_indicator_star] at hleft hright
  obtain ⟨x, _hxmem, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hleft
  obtain ⟨y, _hymem, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hright
  have hAx : x ∈ A := by
    by_contra hnot
    simp [indicator, hnot] at hx
  have hAxt : x - t ∈ A := by
    by_contra hnot
    simp [indicator, hnot] at hx
  have hAy : y ∈ A := by
    by_contra hnot
    simp [indicator, hnot] at hy
  have hAyd : y - (t - d) ∈ A := by
    by_contra hnot
    simp [indicator, hnot] at hy
  exact ⟨{
    a := x
    b := x - t
    c := y
    e := y - (t - d)
    ha := hAx
    hb := hAxt
    hc := hAy
    he := hAyd
    relation := by ring }⟩

private lemma lemma78_representation_of_mem_bohr {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi))) :
    Nonempty (Lemma78Representation A d) :=
  lemma78_representation_of_fourCorrelation_ne_zero A d
    (lemma78_fourCorrelation_ne_zero_of_mem_bohr A alpha halpha hcard d hd)

private lemma lemma78_freiman8_fin_sum {N : Nat}
    (A : Finset (ZMod N)) (phi : ZMod N -> ZMod N)
    (hphi : FreimanHom 8 A phi) (x y : Fin 8 -> ZMod N)
    (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A)
    (hsum : (∑ i, x i) = ∑ i, y i) :
    (∑ i, phi (x i)) = ∑ i, phi (y i) := by
  let sx : Multiset (ZMod N) := Multiset.map x (Finset.univ : Finset (Fin 8)).val
  let sy : Multiset (ZMod N) := Multiset.map y (Finset.univ : Finset (Fin 8)).val
  have hsA : ∀ ⦃z⦄, z ∈ sx -> z ∈ (A : Set (ZMod N)) := by
    intro z hz
    simp only [sx, Multiset.mem_map] at hz
    obtain ⟨i, _hi, rfl⟩ := hz
    exact hx i
  have htA : ∀ ⦃z⦄, z ∈ sy -> z ∈ (A : Set (ZMod N)) := by
    intro z hz
    simp only [sy, Multiset.mem_map] at hz
    obtain ⟨i, _hi, rfl⟩ := hz
    exact hy i
  have hsCard : sx.card = 8 := by simp [sx]
  have htCard : sy.card = 8 := by simp [sy]
  have hsEq : sx.sum = sy.sum := by
    simpa [sx, sy, Fin.sum_univ_succ] using hsum
  have hmap := hphi.map_sum_eq_map_sum hsA htA hsCard htCard hsEq
  simpa [sx, sy, Fin.sum_univ_succ] using hmap

private lemma lemma78_representation_value_wellDefined {N : Nat}
    (A : Finset (ZMod N)) (phi : ZMod N -> ZMod N)
    (hphi : FreimanHom 8 A phi) {d : ZMod N}
    (q q' : Lemma78Representation A d) :
    q.value phi = q'.value phi := by
  let x : Fin 8 -> ZMod N :=
    ![q.a, q.e, q'.b, q'.c, q.a, q.a, q.a, q.a]
  let y : Fin 8 -> ZMod N :=
    ![q'.a, q'.e, q.b, q.c, q.a, q.a, q.a, q.a]
  have hx : ∀ i, x i ∈ A := by
    intro i
    fin_cases i <;> simp [x, q.ha, q.he, q'.hb, q'.hc]
  have hy : ∀ i, y i ∈ A := by
    intro i
    fin_cases i <;> simp [y, q.ha, q'.ha, q'.he, q.hb, q.hc]
  have hsum : (∑ i, x i) = ∑ i, y i := by
    simp [x, y, Fin.sum_univ_succ]
    have hq := q.relation
    have hq' := q'.relation
    linear_combination hq - hq'
  have himage := lemma78_freiman8_fin_sum A phi hphi x y hx hy hsum
  simp [x, y, Fin.sum_univ_succ] at himage
  unfold Lemma78Representation.value
  linear_combination himage

private lemma lemma78_representation_value_additive {N : Nat}
    (A : Finset (ZMod N)) (phi : ZMod N -> ZMod N)
    (hphi : FreimanHom 8 A phi) {d1 d2 d3 d4 : ZMod N}
    (q1 : Lemma78Representation A d1) (q2 : Lemma78Representation A d2)
    (q3 : Lemma78Representation A d3) (q4 : Lemma78Representation A d4)
    (hd : d1 + d2 = d3 + d4) :
    q1.value phi + q2.value phi = q3.value phi + q4.value phi := by
  let x : Fin 8 -> ZMod N :=
    ![q1.a, q1.e, q2.a, q2.e, q3.b, q3.c, q4.b, q4.c]
  let y : Fin 8 -> ZMod N :=
    ![q3.a, q3.e, q4.a, q4.e, q1.b, q1.c, q2.b, q2.c]
  have hx : ∀ i, x i ∈ A := by
    intro i
    fin_cases i <;> simp [x, q1.ha, q1.he, q2.ha, q2.he,
      q3.hb, q3.hc, q4.hb, q4.hc]
  have hy : ∀ i, y i ∈ A := by
    intro i
    fin_cases i <;> simp [y, q3.ha, q3.he, q4.ha, q4.he,
      q1.hb, q1.hc, q2.hb, q2.hc]
  have hsum : (∑ i, x i) = ∑ i, y i := by
    simp [x, y, Fin.sum_univ_succ]
    have h1 := q1.relation
    have h2 := q2.relation
    have h3 := q3.relation
    have h4 := q4.relation
    linear_combination h1 + h2 - h3 - h4 + hd
  have himage := lemma78_freiman8_fin_sum A phi hphi x y hx hy hsum
  simp [x, y, Fin.sum_univ_succ] at himage
  unfold Lemma78Representation.value
  linear_combination himage

private noncomputable def lemma78ChosenRepresentation {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi))) :
    Lemma78Representation A d :=
  Classical.choice (lemma78_representation_of_mem_bohr A alpha halpha hcard d hd)

private noncomputable def lemma78InducedMap {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (phi : ZMod N -> ZMod N)
    (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) : ZMod N -> ZMod N :=
  fun d => if hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi))
    then (lemma78ChosenRepresentation A alpha halpha hcard d hd).value phi
    else 0

private lemma lemma78_induced_freiman {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (phi : ZMod N -> ZMod N)
    (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (hphi : FreimanHom 8 A phi) :
    FreimanHom 2 (bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi)))
      (lemma78InducedMap A phi alpha halpha hcard) := by
  rw [FreimanHom, isAddFreimanHom_two]
  constructor
  · intro x _hx
    exact Set.mem_univ _
  · intro a ha b hb c hc d hd habcd
    change a ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi)) at ha
    change b ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi)) at hb
    change c ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi)) at hc
    change d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi)) at hd
    let qa := lemma78ChosenRepresentation A alpha halpha hcard a ha
    let qb := lemma78ChosenRepresentation A alpha halpha hcard b hb
    let qc := lemma78ChosenRepresentation A alpha halpha hcard c hc
    let qd := lemma78ChosenRepresentation A alpha halpha hcard d hd
    have hadd := lemma78_representation_value_additive A phi hphi qa qb qc qd habcd
    have haMap : lemma78InducedMap A phi alpha halpha hcard a = qa.value phi := by
      rw [lemma78InducedMap, dif_pos ha]
    have hbMap : lemma78InducedMap A phi alpha halpha hcard b = qb.value phi := by
      rw [lemma78InducedMap, dif_pos hb]
    have hcMap : lemma78InducedMap A phi alpha halpha hcard c = qc.value phi := by
      rw [lemma78InducedMap, dif_pos hc]
    have hdMap : lemma78InducedMap A phi alpha halpha hcard d = qd.value phi := by
      rw [lemma78InducedMap, dif_pos hd]
    rw [haMap, hbMap, hcMap, hdMap]
    exact hadd

private lemma lemma78_induced_agrees {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (phi : ZMod N -> ZMod N)
    (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (hphi : FreimanHom 8 A phi)
    (x : ZMod N) (hx : x ∈ A) (y : ZMod N) (hy : y ∈ A)
    (hxy : x - y ∈ bohr (section7Spectrum A alpha)
      (alpha / (32 * Real.pi))) :
    phi x - phi y = lemma78InducedMap A phi alpha halpha hcard (x - y) := by
  let q : Lemma78Representation A (x - y) := {
    a := x
    b := y
    c := x
    e := x
    ha := hx
    hb := hy
    hc := hx
    he := hx
    relation := by ring }
  let q' := lemma78ChosenRepresentation A alpha halpha hcard (x - y) hxy
  have hvalue := lemma78_representation_value_wellDefined A phi hphi q q'
  unfold lemma78InducedMap
  rw [dif_pos hxy]
  change phi x + phi x - phi y - phi x = q'.value phi at hvalue
  linear_combination hvalue

/-- **Gowers, Lemma 7.8.** -/
theorem lemma_7_8_holds : lemma_7_8 := by
  intro N _ A phi alpha halpha hcard hphi
  dsimp only
  constructor
  · exact lemma78_spectrum_card_bound A alpha halpha hcard
  · refine ⟨lemma78InducedMap A phi alpha halpha hcard,
      lemma78_induced_freiman A phi alpha halpha hcard hphi, ?_⟩
    intro x hx y hy hxy
    exact lemma78_induced_agrees A phi alpha halpha hcard hphi x hx y hy hxy

end LeanProofs.GowersSzemeredi
