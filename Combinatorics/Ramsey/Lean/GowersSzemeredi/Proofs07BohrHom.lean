import GowersSzemeredi.Proofs01_03
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GowersSzemeredi.Proofs00ExponentialBounds

/-!
# The Bogolyubov--Freiman homomorphism lemma

This module proves Gowers's Lemma 7.8.  The analytic part truncates the
Fourier inversion formula for the fourfold difference count to the large
spectrum.  The algebraic part uses the order-eight Freiman hypothesis to
make the induced map on `2A-2A` well defined and additive.

`lemma78_alpha_le_one` and `lemma_7_8_group_holds` are in `Proofs07BohrHomSide`,
outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

attribute [simp] exponential_add

attribute [simp] star_exponential

attribute [simp] cor57_norm_exponential

attribute [simp] lemma78_indicator_star

lemma lemma78_spectrum_card_bound {N : Nat} [NeZero N]
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
      rw [← Real.rpow_natCast, ← Real.rpow_mul halpha.le]
      norm_num
    rw [hpow]
    norm_num
  have hscaled :
      (((section7Spectrum A alpha).card : Real) * lambda ^ 2) * (N : Real) ^ 2 <=
        alpha * (N : Real) ^ 2 := by linarith
  have hcancel : ((section7Spectrum A alpha).card : Real) * lambda ^ 2 <= alpha :=
    le_of_mul_le_mul_right hscaled (sq_pos_of_pos hN)
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
  rw [lemma78PairCorrelation, identity_2_1_holds, Complex.star_def, Complex.mul_conj']
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

private lemma lemma78_bohr_phase_bound {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi)))
    (r : ZMod N) (hr : r ∈ section7Spectrum A alpha) :
    ‖exponential (r * d) - 1‖ <= alpha / 16 :=
  (bohr_phase_bound _ _ d hd r hr).trans_eq (by
    rw [show 2 * Real.pi * (alpha / (32 * Real.pi)) = alpha / 16 * (Real.pi / Real.pi) by ring,
      div_self Real.pi_ne_zero, mul_one])

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
              ‖fourier (indicator A) r‖ ^ 2 := by ring
      _ <= ∑ r : ZMod N,
          (A.card : Real) ^ 2 * ‖fourier (indicator A) r‖ ^ 2 := by
        gcongr with r
        exact fourier_indicator_norm_le_card A r
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
      _ <= (lambda * N) ^ 2 * ‖fourier (indicator A) r‖ ^ 2 := by gcongr
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
    rw [← Real.rpow_natCast, ← Real.rpow_mul halpha.le]
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
        gcongr with r _
        dsimp [w, F]
        nlinarith [norm_exponential_sub_one_le_two (r * d),
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
          2 * (alpha * lambda ^ 2 * (N : Real) ^ 4) := by gcongr
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
  have hzero : exponential (0 : ZMod N) = 1 := AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))
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
        ‖fourier (indicator A) r‖ ^ 4 * ‖exponential (r * d) - 1‖ := by norm_num
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
    simpa [fourier_indicator_zero] using hsingle
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

private def Lemma78Representation.value {N : Nat} {G : Type*}
    [AddCommGroup G] {A : Finset (ZMod N)} {d : ZMod N}
    (phi : ZMod N -> G) (q : Lemma78Representation A d) : G :=
  phi q.a + phi q.e - phi q.b - phi q.c

private lemma lemma78_pairCorrelation_star {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (t : ZMod N) :
    star (lemma78PairCorrelation A t) = lemma78PairCorrelation A t := by
  unfold lemma78PairCorrelation correlation
  simp only [star_sum, star_mul, lemma78_indicator_star]
  apply Finset.sum_congr rfl
  intro x _
  ring

private lemma lemma78_representation_of_fourCorrelation_ne_zero
    {N : Nat} [NeZero N] (A : Finset (ZMod N)) (d : ZMod N)
    (hne : lemma78FourCorrelation A d != 0) :
    Nonempty (Lemma78Representation A d) := by
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

private lemma lemma78_freiman8_fin_sum {N : Nat} {G : Type*}
    [AddCommGroup G] (A : Finset (ZMod N)) (phi : ZMod N -> G)
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

private lemma lemma78_representation_value_wellDefined {N : Nat} {G : Type*}
    [AddCommGroup G] (A : Finset (ZMod N)) (phi : ZMod N -> G)
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
  rw [show phi q.a + phi q.e - phi q.b - phi q.c =
      (phi q.a + phi q.e) - (phi q.b + phi q.c) by abel]
  rw [show phi q'.a + phi q'.e - phi q'.b - phi q'.c =
      (phi q'.a + phi q'.e) - (phi q'.b + phi q'.c) by abel]
  apply sub_eq_sub_iff_add_eq_add.mpr
  apply add_right_cancel (b := 4 • phi q.a)
  abel_nf at himage ⊢
  exact himage

private lemma lemma78_representation_value_additive {N : Nat} {G : Type*}
    [AddCommGroup G] (A : Finset (ZMod N)) (phi : ZMod N -> G)
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
  rw [show
    (phi q1.a + phi q1.e - phi q1.b - phi q1.c) +
        (phi q2.a + phi q2.e - phi q2.b - phi q2.c) =
      (phi q1.a + phi q1.e + phi q2.a + phi q2.e) -
        (phi q1.b + phi q1.c + phi q2.b + phi q2.c) by abel]
  rw [show
    (phi q3.a + phi q3.e - phi q3.b - phi q3.c) +
        (phi q4.a + phi q4.e - phi q4.b - phi q4.c) =
      (phi q3.a + phi q3.e + phi q4.a + phi q4.e) -
        (phi q3.b + phi q3.c + phi q4.b + phi q4.c) by abel]
  apply sub_eq_sub_iff_add_eq_add.mpr
  abel_nf at himage ⊢
  exact himage

private noncomputable def lemma78ChosenRepresentation {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi))) :
    Lemma78Representation A d :=
  Classical.choice (lemma78_representation_of_mem_bohr A alpha halpha hcard d hd)

noncomputable def lemma78InducedMap {N : Nat} {G : Type*}
    [NeZero N] [AddCommGroup G] (A : Finset (ZMod N)) (phi : ZMod N -> G)
    (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) : ZMod N -> G :=
  fun d => if hd : d ∈ bohr (section7Spectrum A alpha) (alpha / (32 * Real.pi))
    then (lemma78ChosenRepresentation A alpha halpha hcard d hd).value phi
    else 0

lemma lemma78_induced_freiman {N : Nat} {G : Type*}
    [NeZero N] [AddCommGroup G]
    (A : Finset (ZMod N)) (phi : ZMod N -> G)
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

lemma lemma78_induced_agrees {N : Nat} {G : Type*}
    [NeZero N] [AddCommGroup G]
    (A : Finset (ZMod N)) (phi : ZMod N -> G)
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
  abel_nf at hvalue ⊢
  exact hvalue

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

private lemma lemma78_fourth_moment_lower {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (A.card : Real) ^ 4 ≤ ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4 := by
  have h := Finset.single_le_sum
    (fun r (_ : r ∈ (Finset.univ : Finset (ZMod N))) ↦
      pow_nonneg (norm_nonneg (fourier (indicator A) r)) 4) (Finset.mem_univ 0)
  simpa [fourier_indicator_zero] using h

private lemma lemma78_constant_phase_bound {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (1 / (8 * Real.pi)))
    (r : ZMod N) (hr : r ∈ section7Spectrum A alpha) :
    ‖exponential (r * d) - 1‖ ≤ (1 : Real) / 4 := by
  have hcenter := (Finset.mem_filter.mp hd).2 r hr
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  calc
    _ ≤ 2 * Real.pi * centeredAbs (r * d) / N :=
      cor57_norm_exponential_sub_one_le (r * d)
    _ ≤ (1 : Real) / 4 := by
      apply (div_le_iff₀ hN).mpr
      calc
        _ ≤ 2 * Real.pi * ((1 / (8 * Real.pi)) * N) := by gcongr
        _ = (1 / 4 : Real) * N := by field_simp [Real.pi_ne_zero]; ring

private lemma lemma78_constant_weighted_phase {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (hα : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (1 / (8 * Real.pi))) :
    (∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4 * ‖exponential (r * d) - 1‖) ≤
      (3 / 8 : Real) * ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4 := by
  let K := section7Spectrum A alpha
  let F := fun r : ZMod N ↦ ‖fourier (indicator A) r‖ ^ 4
  let w := fun r : ZMod N ↦ F r * ‖exponential (r * d) - 1‖
  have hmain : (∑ r ∈ Finset.univ.filter (fun r ↦ r ∈ K), w r) ≤
      (1 / 4 : Real) * ∑ r, F r := by
    calc
      _ ≤ ∑ r ∈ Finset.univ.filter (fun r ↦ r ∈ K), (1 / 4 : Real) * F r := by
        apply Finset.sum_le_sum
        intro r hr
        dsimp only [w]
        rw [mul_comm (1 / 4 : Real)]
        exact mul_le_mul_of_nonneg_left
          (lemma78_constant_phase_bound A alpha d hd r (Finset.mem_filter.mp hr).2)
          (by dsimp [F]; positivity)
      _ = (1 / 4 : Real) * ∑ r ∈ Finset.univ.filter (fun r ↦ r ∈ K), F r := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ ↦ by dsimp [F]; positivity)) (by norm_num)
  have htailPhase : (∑ r ∈ Finset.univ.filter (fun r ↦ r ∉ K), w r) ≤
      2 * ∑ r ∈ Finset.univ.filter (fun r ↦ r ∉ K), F r := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    dsimp only [w]
    rw [mul_comm (2 : Real)]
    exact mul_le_mul_of_nonneg_left (norm_exponential_sub_one_le_two (r * d))
      (by dsimp [F]; positivity)
  let lambda := alpha ^ ((3 : Real) / 2) / 4
  have htail := lemma78_small_spectrum_tail A alpha lambda rfl hcard
  rw [lemma78_lambda_sq alpha lambda hα rfl] at htail
  have hzero := lemma78_fourth_moment_lower A
  rw [hcard] at hzero
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod N))
    (fun r ↦ r ∈ K) w
  change (∑ r, w r) ≤ (3 / 8 : Real) * ∑ r, F r
  linarith

private lemma lemma78_constant_correlation_nonzero {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (hα : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (d : ZMod N)
    (hd : d ∈ bohr (section7Spectrum A alpha) (1 / (8 * Real.pi))) :
    lemma78FourCorrelation A d != 0 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let E : Real := ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4
  have hE : 0 < E := by
    have hcardpos : (0 : Real) < A.card := by rw [hcard]; exact mul_pos hα hN
    exact (pow_pos hcardpos 4).trans_le (lemma78_fourth_moment_lower A)
  have hzero : ‖lemma78FourCorrelation A 0‖ = (N : Real)⁻¹ * E := by
    rw [lemma78_fourCorrelation_inversion A 0]
    have hexp : exponential (0 : ZMod N) = 1 :=
      AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))
    simp only [mul_zero, hexp, mul_one]
    rw [← Complex.ofReal_sum, norm_mul, norm_inv, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE.le]
  have hshift : ‖lemma78FourCorrelation A d - lemma78FourCorrelation A 0‖ ≤
      (N : Real)⁻¹ * ((3 / 8 : Real) * E) := by
    rw [lemma78_fourCorrelation_sub_zero, norm_mul, norm_inv, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hN.le)
    calc
      _ ≤ ∑ r : ZMod N, ‖((‖fourier (indicator A) r‖ ^ 4 : Real) : Complex) *
          (exponential (r * d) - 1)‖ := norm_sum_le _ _
      _ = ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4 * ‖exponential (r * d) - 1‖ := by norm_num
      _ ≤ _ := lemma78_constant_weighted_phase A alpha hα hcard d hd
  rw [bne_iff_ne]
  intro hdzero
  rw [hdzero, zero_sub, norm_neg, hzero] at hshift
  have hp : 0 < (N : Real)⁻¹ * E := mul_pos (inv_pos.mpr hN) hE
  nlinarith only [hshift, hp]

private lemma lemma78_induced_on_represented_domain {N : Nat} {G : Type*}
    [AddCommGroup G] (A B : Finset (ZMod N)) (phi : ZMod N → G)
    (hphi : FreimanHom 8 A phi)
    (hrep : ∀ d ∈ B, Nonempty (Lemma78Representation A d)) :
    ∃ psi : ZMod N → G, FreimanHom 2 B psi ∧
      ∀ x ∈ A, ∀ y ∈ A, x - y ∈ B → phi x - phi y = psi (x - y) := by
  let rep := fun d hd ↦ Classical.choice (hrep d hd)
  let psi := fun d ↦ if hd : d ∈ B then (rep d hd).value phi else 0
  refine ⟨psi, ?_, ?_⟩
  · rw [FreimanHom, isAddFreimanHom_two]
    refine ⟨Set.mapsTo_univ _ _, ?_⟩
    intro a ha b hb c hc d hd habcd
    change a ∈ B at ha
    change b ∈ B at hb
    change c ∈ B at hc
    change d ∈ B at hd
    have h := lemma78_representation_value_additive A phi hphi
      (rep a ha) (rep b hb) (rep c hc) (rep d hd) habcd
    simpa only [psi, dif_pos ha, dif_pos hb, dif_pos hc, dif_pos hd] using h
  · intro x hx y hy hxy
    let q : Lemma78Representation A (x - y) :=
      ⟨x, y, x, x, hx, hy, hx, hx, by ring⟩
    have h := lemma78_representation_value_wellDefined A phi hphi q (rep (x - y) hxy)
    dsimp only [psi]
    rw [dif_pos hxy]
    change phi x + phi x - phi y - phi x = (rep (x - y) hxy).value phi at h
    convert h using 1 <;> abel

/-- A constant-radius strengthening of the Bogolyubov--Freiman lemma.
Controlling the error relative to the actual fourth moment removes the
factor of the density from the Bohr radius, without changing the spectrum. -/
theorem lemma_7_8_constant_radius {G : Type*} [AddCommGroup G]
    (N : Nat) [NeZero N] (A : Finset (ZMod N)) (phi : ZMod N → G)
    (alpha : Real) (hα : 0 < alpha) (hcard : (A.card : Real) = alpha * N)
    (hphi : FreimanHom 8 A phi) :
    let K := section7Spectrum A alpha
    (K.card : Real) ≤ 16 * alpha ^ (-(2 : Real)) ∧
      ∃ psi : ZMod N → G, FreimanHom 2 (bohr K (1 / (8 * Real.pi))) psi ∧
        ∀ x ∈ A, ∀ y ∈ A, x - y ∈ bohr K (1 / (8 * Real.pi)) →
          phi x - phi y = psi (x - y) := by
  refine ⟨lemma78_spectrum_card_bound A alpha hα hcard, ?_⟩
  apply lemma78_induced_on_represented_domain A _ phi hphi
  intro d hd
  exact lemma78_representation_of_fourCorrelation_ne_zero A d
    (lemma78_constant_correlation_nonzero A alpha hα hcard d hd)

/-- **Classical Bogolyubov lemma**, extracted from the proof of Lemma 7.8.
For `A ⊆ ℤ/N` of density `α`, the large spectrum `K` has at most `16α⁻²`
elements, and every element of `B(K; 1/(8π))` lies in `2A − 2A`. This is the
polynomial-codimension input for the bilinear Bogolyubov argument (research
notes J.6). -/
theorem bogolyubov_classical {N : Nat} [NeZero N] (A : Finset (ZMod N)) (alpha : Real)
    (hα : 0 < alpha) (hcard : (A.card : Real) = alpha * N) :
    ((section7Spectrum A alpha).card : Real) ≤ 16 * alpha ^ (-(2 : Real)) ∧
      ∀ d ∈ bohr (section7Spectrum A alpha) (1 / (8 * Real.pi)),
        ∃ a ∈ A, ∃ e ∈ A, ∃ b ∈ A, ∃ c ∈ A, d = a + e - b - c := by
  refine ⟨lemma78_spectrum_card_bound A alpha hα hcard, fun d hd => ?_⟩
  obtain ⟨R⟩ := lemma78_representation_of_fourCorrelation_ne_zero A d
    (lemma78_constant_correlation_nonzero A alpha hα hcard d hd)
  exact ⟨R.a, R.ha, R.e, R.he, R.b, R.hb, R.c, R.hc, R.relation.symm⟩

private lemma centeredAbs_add_le {N : Nat} [NeZero N] (x y : ZMod N) :
    centeredAbs (x + y) ≤ centeredAbs x + centeredAbs y := by
  unfold centeredAbs
  calc
    (x + y).valMinAbs.natAbs ≤
        (x.valMinAbs + y.valMinAbs).natAbs :=
      ZMod.natAbs_valMinAbs_add_le x y
    _ ≤ x.valMinAbs.natAbs + y.valMinAbs.natAbs := Int.natAbs_add_le _ _

/-- `|n x| ≤ n |x|` for the centered absolute value. -/
theorem centeredAbs_nsmul_le {N : Nat} [NeZero N] (n : Nat) (x : ZMod N) :
    centeredAbs (n • x) ≤ n * centeredAbs x := by
  induction n with
  | zero => simp [centeredAbs]
  | succ n ih =>
      rw [succ_nsmul, Nat.succ_mul]
      exact le_trans (centeredAbs_add_le (n • x) x) (Nat.add_le_add_right ih _)

/-- **Symmetric multiples of a small Bohr element**: if `d ∈ Bohr(K, ρ/m)` then
`{j d : |j| ≤ m} ⊆ Bohr(K, ρ)`. -/
theorem bohr_symmetric_multiples_subset {p : Nat} [NeZero p]
    (K : Finset (ZMod p)) (rho : Real) (hrho : 0 ≤ rho)
    (m : Nat) (hm : 0 < m) (d : ZMod p)
    (hd : d ∈ bohr K (rho / m)) :
    symmetricMultiples d m ⊆ bohr K rho := by
  intro z hz
  rw [symmetricMultiples, Finset.mem_image] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  rw [bohr, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  rw [bohr, Finset.mem_filter] at hd
  have hdr := hd.2 r hr
  have hbase : 0 <= rho / (m : Real) * p := by positivity
  have hcollapse : (m : Real) * (rho / (m : Real) * p) = rho * p := by
    field_simp
  have hjBounds : -(m : Int) <= j ∧ j <= (m : Int) := Finset.mem_Icc.mp hj
  cases j with
  | ofNat n =>
      have hcastNat : ((Int.ofNat n : Int) : ZMod p) = (n : ZMod p) := by norm_num
      rw [hcastNat]
      have hn : n <= m := by
        apply Int.ofNat_le.mp
        simpa only [Int.ofNat_eq_natCast] using hjBounds.2
      have hcenter : centeredAbs (r * ((n : ZMod p) * d)) <=
          n * centeredAbs (r * d) := by
        have hmul : r * ((n : ZMod p) * d) = n • (r * d) := by ring
        rw [hmul]
        exact centeredAbs_nsmul_le n (r * d)
      calc
        (centeredAbs (r * ((n : ZMod p) * d)) : Real) <=
            n * centeredAbs (r * d) := by exact_mod_cast hcenter
        _ <= n * (rho / (m : Real) * p) := by gcongr
        _ <= m * (rho / (m : Real) * p) := by gcongr
        _ = rho * p := hcollapse
  | negSucc n =>
      have hn : n + 1 <= m := by omega
      have hcast : ((Int.negSucc n : Int) : ZMod p) * d =
          -(((n + 1 : Nat) : ZMod p) * d) := by push_cast; ring
      rw [hcast, mul_neg, centeredAbs_neg]
      have hcenter : centeredAbs (r * (((n + 1 : Nat) : ZMod p) * d)) <=
          (n + 1) * centeredAbs (r * d) := by
        have hmul : r * (((n + 1 : Nat) : ZMod p) * d) =
            (n + 1) • (r * d) := by push_cast; ring
        rw [hmul]
        exact centeredAbs_nsmul_le (n + 1) (r * d)
      calc
        (centeredAbs (r * (((n + 1 : Nat) : ZMod p) * d)) : Real) <=
            (n + 1) * centeredAbs (r * d) := by exact_mod_cast hcenter
        _ <= (n + 1) * (rho / (m : Real) * p) := by gcongr
        _ <= m * (rho / (m : Real) * p) := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hbase
        _ = rho * p := hcollapse

/-- A Freiman map vanishing at zero is additive along `{n d : n ≤ m}`. -/
theorem generic_freiman_map_nat_multiple {p : Nat} {G : Type*}
    [NeZero p] [AddCommGroup G]
    (B : Finset (ZMod p)) (psi : ZMod p -> G)
    (hpsi : FreimanHom 2 B psi) (hpsiZero : psi 0 = 0)
    (d : ZMod p) (m : Nat) (hm : 0 < m)
    (hmem : symmetricMultiples d m ⊆ B) (n : Nat) (hn : n <= m) :
    psi ((n : ZMod p) * d) = n • psi d := by
  have hzero : (0 : ZMod p) ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hd : d ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨1, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hpsi' : IsAddFreimanHom 2 (B : Set (ZMod p)) Set.univ psi := hpsi
  induction n with
  | zero => simpa using hpsiZero
  | succ n ih =>
      have hn' : n <= m := Nat.le_trans (Nat.le_succ n) hn
      have hnm : ((n : ZMod p) * d) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨(n : Int), Finset.mem_Icc.mpr ?_, by simp⟩
        constructor <;> omega
      have hsucc : (((n + 1 : Nat) : ZMod p) * d) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨(n + 1 : Int), Finset.mem_Icc.mpr ?_, by simp⟩
        constructor <;> omega
      have hadd : ((n + 1 : Nat) : ZMod p) * d + 0 =
          (n : ZMod p) * d + d := by push_cast; ring
      have hmap := hpsi'.add_eq_add (hmem hsucc) (hmem hzero)
        (hmem hnm) (hmem hd) hadd
      rw [hpsiZero, add_zero, ih hn'] at hmap
      simpa only [add_nsmul, one_nsmul] using hmap

/-- A Freiman map vanishing at zero is `ℤ`-linear on `{j d : |j| ≤ m}`. -/
theorem generic_freiman_map_int_multiple {p : Nat} {G : Type*}
    [NeZero p] [AddCommGroup G]
    (B : Finset (ZMod p)) (psi : ZMod p -> G)
    (hpsi : FreimanHom 2 B psi) (hpsiZero : psi 0 = 0)
    (d : ZMod p) (m : Nat) (hm : 0 < m)
    (hmem : symmetricMultiples d m ⊆ B) (j : Int)
    (hj : j ∈ Finset.Icc (-(m : Int)) (m : Int)) :
    psi ((j : ZMod p) * d) = j • psi d := by
  have hzero : (0 : ZMod p) ∈ symmetricMultiples d m := by
    rw [symmetricMultiples, Finset.mem_image]
    refine ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩
    constructor <;> omega
  have hpsi' : IsAddFreimanHom 2 (B : Set (ZMod p)) Set.univ psi := hpsi
  cases j with
  | ofNat n =>
      have hn : n <= m := by
        have := (Finset.mem_Icc.mp hj).2
        apply Int.ofNat_le.mp
        simpa only [Int.ofNat_eq_natCast] using this
      simpa using generic_freiman_map_nat_multiple B psi hpsi hpsiZero d m hm hmem n hn
  | negSucc n =>
      have hn : n + 1 <= m := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      have hpos : (((n + 1 : Nat) : ZMod p) * d) ∈ symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨(n + 1 : Int), Finset.mem_Icc.mpr ?_, by simp⟩
        constructor <;> omega
      have hneg : (-(((n + 1 : Nat) : ZMod p) * d)) ∈
          symmetricMultiples d m := by
        rw [symmetricMultiples, Finset.mem_image]
        refine ⟨Int.negSucc n, Finset.mem_Icc.mpr ?_, ?_⟩
        · constructor <;> omega
        · push_cast
          ring
      have hadd : -(((n + 1 : Nat) : ZMod p) * d) +
          ((n + 1 : Nat) : ZMod p) * d = 0 + 0 := by ring
      have hmap := hpsi'.add_eq_add (hmem hneg) (hmem hpos)
        (hmem hzero) (hmem hzero) hadd
      have hnat := generic_freiman_map_nat_multiple B psi hpsi hpsiZero
        d m hm hmem (n + 1) hn
      rw [hpsiZero, add_zero, hnat] at hmap
      have hnegValue : psi (-(((n + 1 : Nat) : ZMod p) * d)) =
          -((n + 1) • psi d) := eq_neg_of_add_eq_zero_left hmap
      convert hnegValue using 1
      · push_cast
        ring_nf
      · simp [add_nsmul]

end LeanProofs.GowersSzemeredi
