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
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have ht : (alpha ^ ((3 : Real) / 2)) ^ 2 = alpha ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul halpha.le]
    norm_num
  have hsum : ((section7Spectrum A alpha).card : Real) *
      (alpha ^ ((3 : Real) / 2) * N / 4) ^ 2 ≤ alpha * (N : Real) ^ 2 := by
    calc _ ≤ ∑ r ∈ section7Spectrum A alpha, ‖fourier (indicator A) r‖ ^ 2 := by
          rw [← nsmul_eq_mul]
          refine Finset.card_nsmul_le_sum _ _ _ fun r hr => ?_
          gcongr
          exact (Finset.mem_filter.mp hr).2
      _ ≤ ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
      _ = alpha * (N : Real) ^ 2 := by rw [lemma78_fourier_indicator_energy, hcard]; ring
  rw [div_pow, mul_pow, ht] at hsum
  rw [Real.rpow_neg halpha.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact le_of_mul_le_mul_right (by linarith) (by positivity : 0 < alpha * (N : Real) ^ 2)

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
  let F := fun r : ZMod N ↦ ‖fourier (indicator A) r‖ ^ 4
  let w := fun r : ZMod N ↦ F r * ‖exponential (r * d) - 1‖
  have hmain : (∑ r ∈ Finset.univ.filter (fun r ↦ r ∈ K), w r) ≤
      (alpha / 16) * ∑ r, F r := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun r hr => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun _ _ _ ↦ by dsimp [F]; positivity)
    rw [mul_comm (alpha / 16)]
    exact mul_le_mul_of_nonneg_left
      (lemma78_bohr_phase_bound A alpha d hd r (Finset.mem_filter.mp hr).2)
      (by dsimp [F]; positivity)
  have htailPhase : (∑ r ∈ Finset.univ.filter (fun r ↦ r ∉ K), w r) ≤
      2 * ∑ r ∈ Finset.univ.filter (fun r ↦ r ∉ K), F r := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [mul_comm (2 : Real)]
    exact mul_le_mul_of_nonneg_left (norm_exponential_sub_one_le_two (r * d))
      (by dsimp [F]; positivity)
  have htotal := mul_le_mul_of_nonneg_left (lemma78_fourth_moment_upper A alpha hcard)
    (by positivity : (0 : Real) ≤ alpha / 16)
  have htail := lemma78_small_spectrum_tail A alpha lambda hlambda hcard
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod N))
    (fun r ↦ r ∈ K) w
  rw [lemma78_lambda_sq alpha lambda halpha hlambda] at htail ⊢
  change (∑ r, w r) ≤ _
  linarith

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
  have hsum : 0 ≤ ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4 := by positivity
  have hzero : (A.card : Real) ^ 4 ≤ ∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 4 := by
    simpa [fourier_indicator_zero] using Finset.single_le_sum
      (fun r (_ : r ∈ (Finset.univ : Finset (ZMod N))) ↦
        pow_nonneg (norm_nonneg (fourier (indicator A) r)) 4) (Finset.mem_univ 0)
  rw [lemma78_fourCorrelation_inversion A 0]
  simp only [mul_zero, exponential_zero, mul_one]
  rw [← Complex.ofReal_sum, norm_mul, norm_inv, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hzero (by positivity))
  rw [lemma78_lambda_sq alpha lambda halpha hlambda, hcard]
  field_simp [ne_of_gt hN]
  nlinarith [sq_nonneg (alpha ^ 2 * (N : Real) ^ 2)]

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
  -- a nonzero correlation has a nonzero term; a nonzero indicator value is a point of `A`
  have hmem (z : ZMod N) (hz : indicator A z ≠ 0) : z ∈ A := by simpa [indicator] using hz
  rw [bne_iff_ne] at hne
  unfold lemma78FourCorrelation correlation at hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [lemma78_pairCorrelation_star] at ht
  obtain ⟨hl, hr⟩ := mul_ne_zero_iff.mp ht
  unfold lemma78PairCorrelation correlation at hl hr
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  rw [lemma78_indicator_star] at hx hy
  exact ⟨⟨x, x - t, y, y - (t - d), hmem _ (left_ne_zero_of_mul hx),
    hmem _ (right_ne_zero_of_mul hx), hmem _ (left_ne_zero_of_mul hy),
    hmem _ (right_ne_zero_of_mul hy), by ring⟩⟩

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
  simpa [Fin.sum_univ_succ] using hphi.map_sum_eq_map_sum (s := Finset.univ.val.map x)
    (t := Finset.univ.val.map y) (Multiset.forall_mem_map_iff.2 fun i _ => hx i)
    (Multiset.forall_mem_map_iff.2 fun i _ => hy i) (by simp) (by simp)
    (by simpa [Fin.sum_univ_succ] using hsum)

private lemma lemma78_representation_value_wellDefined {N : Nat} {G : Type*}
    [AddCommGroup G] (A : Finset (ZMod N)) (phi : ZMod N -> G)
    (hphi : FreimanHom 8 A phi) {d : ZMod N}
    (q q' : Lemma78Representation A d) :
    q.value phi = q'.value phi := by
  -- `q.a + q.e + q'.b + q'.c = q'.a + q'.e + q.b + q.c`, padded by four copies of `q.a`
  let x : Fin 8 -> ZMod N := ![q.a, q.e, q'.b, q'.c, q.a, q.a, q.a, q.a]
  let y : Fin 8 -> ZMod N := ![q'.a, q'.e, q.b, q.c, q.a, q.a, q.a, q.a]
  have h := lemma78_freiman8_fin_sum A phi hphi x y
    (fun i => by fin_cases i <;> simp [x, q.ha, q.he, q'.hb, q'.hc])
    (fun i => by fin_cases i <;> simp [y, q.ha, q'.ha, q'.he, q.hb, q.hc])
    (by simp [x, y, Fin.sum_univ_succ]; linear_combination q.relation - q'.relation)
  simp [x, y, Fin.sum_univ_succ] at h
  unfold Lemma78Representation.value
  rw [← sub_eq_zero, ← sub_eq_zero.mpr h]
  abel

private lemma lemma78_representation_value_additive {N : Nat} {G : Type*}
    [AddCommGroup G] (A : Finset (ZMod N)) (phi : ZMod N -> G)
    (hphi : FreimanHom 8 A phi) {d1 d2 d3 d4 : ZMod N}
    (q1 : Lemma78Representation A d1) (q2 : Lemma78Representation A d2)
    (q3 : Lemma78Representation A d3) (q4 : Lemma78Representation A d4)
    (hd : d1 + d2 = d3 + d4) :
    q1.value phi + q2.value phi = q3.value phi + q4.value phi := by
  let x : Fin 8 -> ZMod N := ![q1.a, q1.e, q2.a, q2.e, q3.b, q3.c, q4.b, q4.c]
  let y : Fin 8 -> ZMod N := ![q3.a, q3.e, q4.a, q4.e, q1.b, q1.c, q2.b, q2.c]
  have h := lemma78_freiman8_fin_sum A phi hphi x y
    (fun i => by
      fin_cases i <;> simp [x, q1.ha, q1.he, q2.ha, q2.he, q3.hb, q3.hc, q4.hb, q4.hc])
    (fun i => by
      fin_cases i <;> simp [y, q3.ha, q3.he, q4.ha, q4.he, q1.hb, q1.hc, q2.hb, q2.hc])
    (by
      simp [x, y, Fin.sum_univ_succ]
      linear_combination q1.relation + q2.relation - q3.relation - q4.relation + hd)
  simp [x, y, Fin.sum_univ_succ] at h
  unfold Lemma78Representation.value
  rw [← sub_eq_zero, ← sub_eq_zero.mpr h]
  abel

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
  refine ⟨Set.mapsTo_univ _ _, fun a ha b hb c hc d hd habcd => ?_⟩
  rw [Finset.mem_coe] at ha hb hc hd
  simp only [lemma78InducedMap, dif_pos ha, dif_pos hb, dif_pos hc, dif_pos hd]
  exact lemma78_representation_value_additive A phi hphi _ _ _ _ habcd

lemma lemma78_induced_agrees {N : Nat} {G : Type*}
    [NeZero N] [AddCommGroup G]
    (A : Finset (ZMod N)) (phi : ZMod N -> G)
    (alpha : Real) (halpha : 0 < alpha)
    (hcard : (A.card : Real) = alpha * N) (hphi : FreimanHom 8 A phi)
    (x : ZMod N) (hx : x ∈ A) (y : ZMod N) (hy : y ∈ A)
    (hxy : x - y ∈ bohr (section7Spectrum A alpha)
      (alpha / (32 * Real.pi))) :
    phi x - phi y = lemma78InducedMap A phi alpha halpha hcard (x - y) := by
  rw [lemma78InducedMap, dif_pos hxy, ← lemma78_representation_value_wellDefined A phi hphi
    (⟨x, y, x, x, hx, hy, hx, hx, by ring⟩ : Lemma78Representation A (x - y))]
  simp only [Lemma78Representation.value]
  abel

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
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun r hr => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun _ _ _ ↦ by dsimp [F]; positivity)
    exact (mul_le_mul_of_nonneg_left (lemma78_constant_phase_bound A alpha d hd r
      (Finset.mem_filter.mp hr).2) (by dsimp [F]; positivity)).trans_eq (mul_comm _ _)
  have htailPhase : (∑ r ∈ Finset.univ.filter (fun r ↦ r ∉ K), w r) ≤
      2 * ∑ r ∈ Finset.univ.filter (fun r ↦ r ∉ K), F r := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => (mul_le_mul_of_nonneg_left
      (norm_exponential_sub_one_le_two (r * d)) (by dsimp [F]; positivity)).trans_eq
        (mul_comm _ _)
  have htail := lemma78_small_spectrum_tail A alpha _ rfl hcard
  rw [lemma78_lambda_sq alpha _ hα rfl] at htail
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
  refine ⟨psi, ?_, fun x hx y hy hxy => ?_⟩
  · rw [FreimanHom, isAddFreimanHom_two]
    refine ⟨Set.mapsTo_univ _ _, fun a ha b hb c hc d hd habcd => ?_⟩
    rw [Finset.mem_coe] at ha hb hc hd
    simp only [psi, dif_pos ha, dif_pos hb, dif_pos hc, dif_pos hd]
    exact lemma78_representation_value_additive A phi hphi _ _ _ _ habcd
  · simp only [psi, dif_pos hxy]
    rw [← lemma78_representation_value_wellDefined A phi hphi
      (⟨x, y, x, x, hx, hy, hx, hx, by ring⟩ : Lemma78Representation A (x - y))]
    simp only [Lemma78Representation.value]
    abel

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
  rw [bohr, Finset.mem_filter] at hd ⊢
  refine ⟨Finset.mem_univ _, fun r hr => ?_⟩
  have hjm := Finset.mem_Icc.mp hj
  obtain ⟨n, hn, hcenter⟩ : ∃ n : Nat, n ≤ m ∧
      centeredAbs (r * ((j : ZMod p) * d)) ≤ n * centeredAbs (r * d) := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
    · exact ⟨n, by omega, by
        simpa [nsmul_eq_mul, mul_left_comm] using centeredAbs_nsmul_le n (r * d)⟩
    · exact ⟨n, by omega, by
        simpa [nsmul_eq_mul, mul_left_comm, centeredAbs_neg] using centeredAbs_nsmul_le n (r * d)⟩
  calc (centeredAbs (r * ((j : ZMod p) * d)) : Real) ≤ n * centeredAbs (r * d) := by
        exact_mod_cast hcenter
    _ ≤ n * (rho / m * p) := by
        gcongr
        exact hd.2 r hr
    _ ≤ m * (rho / m * p) := by gcongr
    _ = rho * p := by field_simp

/-- A Freiman map vanishing at zero is additive along `{n d : n ≤ m}`. -/
theorem generic_freiman_map_nat_multiple {p : Nat} {G : Type*}
    [NeZero p] [AddCommGroup G]
    (B : Finset (ZMod p)) (psi : ZMod p -> G)
    (hpsi : FreimanHom 2 B psi) (hpsiZero : psi 0 = 0)
    (d : ZMod p) (m : Nat) (hm : 0 < m)
    (hmem : symmetricMultiples d m ⊆ B) (n : Nat) (hn : n <= m) :
    psi ((n : ZMod p) * d) = n • psi d := by
  have hB (i : Nat) (hi : i ≤ m) : (i : ZMod p) * d ∈ B :=
    hmem (Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩)
  induction n with
  | zero => simpa using hpsiZero
  | succ n ih =>
      -- `(n + 1) d + 0 = n d + d`
      have h := IsAddFreimanHom.add_eq_add hpsi (hB (n + 1) hn) (hB 0 (Nat.zero_le m))
        (hB n (by omega)) (hB 1 hm) (by push_cast; ring)
      rw [Nat.cast_zero, zero_mul, hpsiZero, add_zero, ih (by omega), Nat.cast_one,
        one_mul] at h
      exact h.trans (succ_nsmul (psi d) n).symm

/-- A Freiman map vanishing at zero is `ℤ`-linear on `{j d : |j| ≤ m}`. -/
theorem generic_freiman_map_int_multiple {p : Nat} {G : Type*}
    [NeZero p] [AddCommGroup G]
    (B : Finset (ZMod p)) (psi : ZMod p -> G)
    (hpsi : FreimanHom 2 B psi) (hpsiZero : psi 0 = 0)
    (d : ZMod p) (m : Nat) (hm : 0 < m)
    (hmem : symmetricMultiples d m ⊆ B) (j : Int)
    (hj : j ∈ Finset.Icc (-(m : Int)) (m : Int)) :
    psi ((j : ZMod p) * d) = j • psi d := by
  have hjm := Finset.mem_Icc.mp hj
  have hB (i : Int) (hi : -(m : Int) ≤ i ∧ i ≤ m) : (i : ZMod p) * d ∈ B :=
    hmem (Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr hi, rfl⟩)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · simpa using generic_freiman_map_nat_multiple B psi hpsi hpsiZero d m hm hmem n (by omega)
  · have hmap := IsAddFreimanHom.add_eq_add hpsi (hB (-n) (by omega)) (hB n (by omega))
      (hB 0 (by omega)) (hB 0 (by omega)) (by push_cast; ring)
    simp only [Int.cast_zero, zero_mul, hpsiZero, add_zero, Int.cast_neg, Int.cast_natCast,
      generic_freiman_map_nat_multiple B psi hpsi hpsiZero d m hm hmem n (by omega)] at hmap
    rw [Int.cast_neg, Int.cast_natCast, neg_zsmul, natCast_zsmul]
    exact eq_neg_of_add_eq_zero_left hmap

end LeanProofs.GowersSzemeredi
