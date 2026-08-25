import FabiusFunction.FourierProduct
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Poisson summation and the partition of unity

This file formalizes Theorem 5 and equations (25)--(32) of Arias de Reyna,
*An infinitely differentiable function with compact support: definition and
properties* (arXiv:1702.05442).

There are two typographical errors in the source which matter to the formal
statements below.

* In (25), the exponential must depend on `t`: its exponent is
  `2 * π * i * k * t / u`.  This is forced by the Fourier-coefficient
  computation in the proof and by the specialization (29).
* In (32), after multiplying (31) by `a`, the factor `1 / a` on the right
  disappears.  We state both the unmultiplied identity and the corrected
  multiplied identity.

The same Schwartz realization also yields a public rapid-decay estimate for
every real-axis derivative of `rvachevFourier`.  The support specialization is
proved on the full sharp ray `a ≥ 1 / 2`; source-compatible wrappers retain the
paper's unnecessary upper bound `a ≤ 1`.  Sign-invariant companions cover the
sharp condition `1 / 2 ≤ |a|` and Poisson summation at zero is exposed for
every nonzero oriented lattice spacing.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Filter MeasureTheory Set

namespace Fabius

noncomputable section

/-- The Schwartz function obtained by positively rescaling Rvachev's compactly
supported smooth function. -/
private noncomputable def scaledRvachevSchwartz
    (F : BoundedFabius) (hF : IsFabius F) (u : ℝ) (hu : u ≠ 0) : SchwartzMap ℝ ℂ := by
  let f : ℝ → ℝ := fun x ↦ rvachevUp F (u * x)
  have hf_compact : HasCompactSupport f := by
    simpa only [f, smul_eq_mul] using
      (rvachevUp_hasCompactSupport F hF).comp_smul hu
  have hf_smooth : ContDiff ℝ ∞ f := by
    dsimp only [f]
    exact (rvachev_contDiff F hF).comp (by fun_prop)
  exact (hf_compact.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hf_smooth)

private lemma scaledRvachevSchwartz_apply
    (F : BoundedFabius) (hF : IsFabius F) (u : ℝ) (hu : u ≠ 0) (x : ℝ) :
    scaledRvachevSchwartz F hF u hu x = (rvachevUp F (u * x) : ℂ) :=
  rfl

private lemma fourier_scaledRvachevSchwartz
    (F : BoundedFabius) (hF : IsFabius F) {u : ℝ} (hu : 0 < u) (w : ℝ) :
    𝓕 (scaledRvachevSchwartz F hF u hu.ne') w =
      (u⁻¹ : ℝ) • rvachevFourier F (((w / u : ℝ) : ℂ)) := by
  rw [SchwartzMap.fourier_coe]
  rw [Real.fourier_real_eq_integral_exp_smul]
  let q : ℝ → ℂ := fun y ↦
    Complex.exp (((-2 * Real.pi * y * (w / u) : ℝ) : ℂ) * Complex.I) *
      (rvachevUp F y : ℂ)
  calc
    (∫ v : ℝ, Complex.exp (((-2 * Real.pi * v * w : ℝ) : ℂ) * Complex.I) •
        scaledRvachevSchwartz F hF u hu.ne' v) =
        ∫ v : ℝ, q (u * v) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [scaledRvachevSchwartz_apply]
      dsimp only [q]
      simp only [smul_eq_mul]
      congr 2
      push_cast
      field_simp [hu.ne']
    _ = |u⁻¹| • ∫ y : ℝ, q y :=
      MeasureTheory.Measure.integral_comp_mul_left q u
    _ = (u⁻¹ : ℝ) • rvachevFourier F (((w / u : ℝ) : ℂ)) := by
      rw [abs_of_pos (inv_pos.mpr hu)]
      congr 1
      unfold rvachevFourier
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [q]
      push_cast
      ring_nf

/-- Every derivative of the real-axis Fourier transform of Rvachev's function
is rapidly decreasing. -/
theorem rvachevFourier_real_iteratedDeriv_rapidDecay
    (F : BoundedFabius) (hF : IsFabius F) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      |x| ^ k *
          ‖iteratedDeriv n (fun t : ℝ => rvachevFourier F (t : ℂ)) x‖ ≤ C := by
  let φ : SchwartzMap ℝ ℂ :=
    scaledRvachevSchwartz F hF 1 (by norm_num)
  let ψ : SchwartzMap ℝ ℂ := 𝓕 φ
  have hfun : (fun t : ℝ => rvachevFourier F (t : ℂ)) = (ψ : ℝ → ℂ) := by
    funext t
    dsimp only [ψ, φ]
    rw [fourier_scaledRvachevSchwartz F hF (by norm_num : (0 : ℝ) < 1)]
    norm_num
  rw [hfun]
  obtain ⟨C, hC, hbound⟩ := ψ.decay k n
  refine ⟨C, hC, ?_⟩
  intro x
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
    hbound x

/-- The Fourier transform of Rvachev's function is rapidly decreasing on the
real axis. -/
theorem rvachevFourier_real_rapidDecay
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      |x| ^ k * ‖rvachevFourier F (x : ℂ)‖ ≤ C := by
  simpa only [iteratedDeriv_zero] using
    rvachevFourier_real_iteratedDeriv_rapidDecay F hF k 0

/-- Corrected equation (25), i.e. Poisson summation for Rvachev's function.
The printed exponential in the source accidentally omits the factor `t`. -/
theorem rvachev_poisson_summation
    (F : BoundedFabius) (hF : IsFabius F) {u : ℝ} (hu : 0 < u) (t : ℝ) :
    (∑' k : ℤ, (rvachevUp F (t + u * k) : ℂ)) =
      ∑' k : ℤ, ((u⁻¹ : ℝ) : ℂ) *
        rvachevFourier F ((((k : ℝ) / u : ℝ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t / u : ℂ)) := by
  have hpoisson :=
    (scaledRvachevSchwartz F hF u hu.ne').tsum_eq_tsum_fourier (t / u)
  calc
    (∑' k : ℤ, (rvachevUp F (t + u * k) : ℂ)) =
        ∑' k : ℤ, scaledRvachevSchwartz F hF u hu.ne' (t / u + k) := by
      apply tsum_congr
      intro k
      rw [scaledRvachevSchwartz_apply]
      congr 2
      field_simp [hu.ne']
    _ = ∑' k : ℤ, 𝓕 (scaledRvachevSchwartz F hF u hu.ne') (k : ℝ) *
        fourier k ((t / u : ℝ) : UnitAddCircle) := hpoisson
    _ = ∑' k : ℤ, ((u⁻¹ : ℝ) : ℂ) *
        rvachevFourier F ((((k : ℝ) / u : ℝ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t / u : ℂ)) := by
      apply tsum_congr
      intro k
      rw [fourier_scaledRvachevSchwartz F hF hu]
      simp only [fourier_coe_apply, Complex.real_smul]
      push_cast
      ring_nf

/-- Equation (26), first in the complex-valued form naturally produced by
Poisson summation.  The positivity hypothesis records the implicit `n ≥ 1`
condition in the paper. -/
private lemma rvachev_partition_one_over_nat_complex
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (∑' k : ℤ, (rvachevUp F (t + (k : ℝ) / n) : ℂ)) = (n : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have h := rvachev_poisson_summation F hF (u := (n : ℝ)⁻¹)
    (inv_pos.mpr hnR) t
  calc
    (∑' k : ℤ, (rvachevUp F (t + (k : ℝ) / n) : ℂ)) =
        ∑' k : ℤ, (rvachevUp F (t + (n : ℝ)⁻¹ * k) : ℂ) := by
      apply tsum_congr
      intro k
      congr 3
      field_simp [hn0]
    _ = ∑' k : ℤ, ((((n : ℝ)⁻¹)⁻¹ : ℝ) : ℂ) *
        rvachevFourier F ((((k : ℝ) / (n : ℝ)⁻¹ : ℝ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
            (t / (n : ℝ)⁻¹ : ℂ)) := h
    _ = (n : ℂ) := by
      rw [tsum_eq_single 0]
      · simp [rvachevFourier_zero F hF]
      · intro k hk
        have hkn : k * (n : ℤ) ≠ 0 := mul_ne_zero hk (by exact_mod_cast hn.ne')
        have harg : ((((k : ℝ) / (n : ℝ)⁻¹ : ℝ) : ℂ)) =
            ((k * (n : ℤ) : ℤ) : ℂ) := by
          push_cast
          field_simp [hn0]
        rw [harg, rvachevFourier_int_eq_zero F hF (k * (n : ℤ)) hkn]
        simp

/-- Equation (26): the translates on the mesh `1 / n` form the constant
partition with value `n`. -/
theorem rvachev_partition_one_over_nat
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ∑' k : ℤ, rvachevUp F (t + (k : ℝ) / n) = n := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_tsum, Complex.ofReal_natCast] using
    rvachev_partition_one_over_nat_complex F hF n hn t

/-- Equation (27): the integer translates of Rvachev's function form a
partition of unity. -/
theorem rvachev_partition_unity
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    ∑' k : ℤ, rvachevUp F (t + k) = 1 := by
  simpa using rvachev_partition_one_over_nat F hF 1 (by omega) t

/-- Equation (28), the two-term form of the partition of unity on `[0, 1]`. -/
theorem rvachev_add_shift_eq_one
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rvachevUp F t + rvachevUp F (t - 1) = 1 := by
  have h := rvachev_partition_unity F hF t
  rw [tsum_eq_sum (s := {(-1 : ℤ), 0})] at h
  · simpa [sub_eq_add_neg, add_comm] using h
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rcases (show k ≤ -2 ∨ 1 ≤ k by omega) with hkneg | hkpos
    · rw [rvachevUp_eq_zero_of_le_neg_one F hF]
      have hknegR : (k : ℝ) ≤ -2 := by exact_mod_cast hkneg
      linarith
    · rw [rvachevUp_eq_zero_of_one_le F hF]
      have hkposR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      linarith

/-- Equation (29), the period-two Fourier expansion obtained from (25). -/
theorem rvachev_even_translate_fourier
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    (∑' k : ℤ, (rvachevUp F (t + 2 * k) : ℂ)) =
      (2 : ℂ)⁻¹ * ∑' k : ℤ,
        rvachevFourier F ((((k : ℝ) / 2 : ℝ) : ℂ)) *
          Complex.exp (Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) := by
  calc
    (∑' k : ℤ, (rvachevUp F (t + 2 * k) : ℂ)) =
        ∑' k : ℤ, (((2 : ℝ)⁻¹ : ℝ) : ℂ) *
          rvachevFourier F ((((k : ℝ) / 2 : ℝ) : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t / 2 : ℂ)) :=
      rvachev_poisson_summation F hF (by norm_num : (0 : ℝ) < 2) t
    _ = (2 : ℂ)⁻¹ * ∑' k : ℤ,
        rvachevFourier F ((((k : ℝ) / 2 : ℝ) : ℂ)) *
          Complex.exp (Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      push_cast
      have hexp :
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t / 2 : ℂ)) =
            Complex.exp (Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) := by
        congr 1
        ring
      rw [hexp]
      norm_num
      ring

private lemma rvachevFourier_half_int_summable
    (F : BoundedFabius) (hF : IsFabius F) :
    Summable fun k : ℤ ↦ rvachevFourier F ((((k : ℝ) / 2 : ℝ) : ℂ)) := by
  let φ : SchwartzMap ℝ ℂ :=
    scaledRvachevSchwartz F hF 2 (by norm_num)
  have hφ : Summable fun k : ℤ ↦ 𝓕 φ (k : ℝ) := by
    exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 φ).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  have htwo := hφ.mul_left (2 : ℂ)
  apply htwo.congr
  intro k
  dsimp only [φ]
  rw [fourier_scaledRvachevSchwartz F hF (by norm_num : (0 : ℝ) < 2)]
  simp only [Complex.real_smul]
  norm_num
  ring

private lemma rvachevFourier_phase_summable
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    Summable fun k : ℤ ↦
      rvachevFourier F ((((k : ℝ) / 2 : ℝ) : ℂ)) *
        Complex.exp (Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) := by
  refine (rvachevFourier_half_int_summable F hF).norm.of_norm_bounded fun k ↦ ?_
  rw [norm_mul]
  have hexp : Real.pi * Complex.I * (k : ℂ) * (t : ℂ) =
      (((Real.pi * (k : ℝ) * t : ℝ) : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [hexp, Complex.norm_exp_ofReal_mul_I, mul_one]

private lemma exp_add_exp_neg_eq_two_mul_cos (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) +
        Complex.exp ((-x : ℝ) * Complex.I) =
      2 * (Real.cos x : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos]
  ring

private lemma rvachev_fourier_phase_pair
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) (n : ℕ) :
    rvachevFourier F ((((n : ℝ) / 2 : ℝ) : ℂ)) *
          Complex.exp (Real.pi * Complex.I * (n : ℂ) * (t : ℂ)) +
        rvachevFourier F ((((-(n : ℤ) : ℤ) : ℝ) / 2 : ℝ) : ℂ) *
          Complex.exp (Real.pi * Complex.I * (-(n : ℤ) : ℂ) * (t : ℂ)) =
      2 * rvachevFourier F ((((n : ℝ) / 2 : ℝ) : ℂ)) *
        (Real.cos (Real.pi * n * t) : ℂ) := by
  have hneg :
      rvachevFourier F ((((-(n : ℤ) : ℤ) : ℝ) / 2 : ℝ) : ℂ) =
        rvachevFourier F ((((n : ℝ) / 2 : ℝ) : ℂ)) := by
    rw [show ((((-(n : ℤ) : ℤ) : ℝ) / 2 : ℝ) : ℂ) =
      -((((n : ℝ) / 2 : ℝ) : ℂ)) by push_cast; ring,
      rvachevFourier_neg F hF]
  rw [hneg]
  have hpos_exp : Real.pi * Complex.I * (n : ℂ) * (t : ℂ) =
      (((Real.pi * n * t : ℝ) : ℂ)) * Complex.I := by
    push_cast
    ring
  have hneg_exp : Real.pi * Complex.I * (-(n : ℤ) : ℂ) * (t : ℂ) =
      (((-(Real.pi * n * t) : ℝ) : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [hpos_exp, hneg_exp, ← mul_add,
    exp_add_exp_neg_eq_two_mul_cos (Real.pi * n * t)]
  ring

/-- On the support interval, every noncentral translate by an even integer
vanishes, so the period-two translate sum reduces to its central term. -/
theorem rvachev_even_translate_sum_eq_self
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    ∑' k : ℤ, rvachevUp F (t + 2 * k) = rvachevUp F t := by
  rw [tsum_eq_single 0]
  · norm_num
  · intro k hk
    rcases (show k ≤ -1 ∨ 1 ≤ k by omega) with hkneg | hkpos
    · rw [rvachevUp_eq_zero_of_le_neg_one F hF]
      have hknegR : (k : ℝ) ≤ -1 := by exact_mod_cast hkneg
      linarith
    · rw [rvachevUp_eq_zero_of_one_le F hF]
      have hkposR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      linarith

/-- Equation (30), the cosine expansion on the support interval. -/
theorem rvachev_cosine_series
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ}
    (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    (rvachevUp F t : ℂ) = (2 : ℂ)⁻¹ +
      ∑' k : ℕ,
        rvachevFourier F (((((2 * k + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) *
          (Real.cos ((2 * k + 1) * Real.pi * t) : ℂ) := by
  let f : ℤ → ℂ := fun n ↦
    rvachevFourier F ((((n : ℝ) / 2 : ℝ) : ℂ)) *
      Complex.exp (Real.pi * Complex.I * (n : ℂ) * (t : ℂ))
  let q : ℕ → ℂ := fun n ↦ f (n : ℤ) + f (-(n : ℤ))
  let c : ℕ → ℂ := fun k ↦
    rvachevFourier F (((((2 * k + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) *
      (Real.cos (Real.pi * (2 * k + 1) * t) : ℂ)
  have hf : Summable f := by
    simpa only [f] using rvachevFourier_phase_summable F hF t
  have hq : Summable q := by
    simpa only [q] using hf.nat_add_neg
  have hpair (n : ℕ) :
      q n = 2 * rvachevFourier F ((((n : ℝ) / 2 : ℝ) : ℂ)) *
        (Real.cos (Real.pi * n * t) : ℂ) := by
    simpa [q, f] using rvachev_fourier_phase_pair F hF t n
  have hq_even : Summable (q ∘ fun k : ℕ ↦ 2 * k) :=
    hq.comp_injective (show Function.Injective (fun k : ℕ ↦ 2 * k) by
      intro i j hij
      exact Nat.mul_left_cancel (by omega) hij)
  have hq_odd : Summable (q ∘ fun k : ℕ ↦ 2 * k + 1) :=
    hq.comp_injective (show Function.Injective (fun k : ℕ ↦ 2 * k + 1) by
      intro i j hij
      exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel hij))
  have heven : ∑' k : ℕ, q (2 * k) = 2 := by
    rw [tsum_eq_single 0]
    · simp [q, f, rvachevFourier_zero F hF]
      ring
    · intro k hk
      rw [hpair]
      have hkInt : (k : ℤ) ≠ 0 := by exact_mod_cast hk
      have harg : (((((2 * k : ℕ) : ℝ) / 2 : ℝ) : ℂ)) =
          ((k : ℤ) : ℂ) := by
        push_cast
        norm_num
      rw [harg, rvachevFourier_int_eq_zero F hF (k : ℤ) hkInt]
      simp
  have hodd : ∑' k : ℕ, q (2 * k + 1) = 2 * ∑' k : ℕ, c k := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [hpair]
    dsimp only [c]
    have hcos : Real.pi * ((2 * k + 1 : ℕ) : ℝ) * t =
        (Real.pi * (2 * (k : ℝ) + 1) * t) := by
      push_cast
      ring
    rw [hcos]
    ring
  have hsplit := tsum_even_add_odd hq_even hq_odd
  have hnat : (∑' n : ℕ, q n) = (∑' n : ℤ, f n) + f 0 := by
    simpa only [q] using tsum_nat_add_neg hf
  have hf0 : f 0 = 1 := by
    simp [f, rvachevFourier_zero F hF]
  have hz : (∑' n : ℤ, f n) = 1 + 2 * ∑' k : ℕ, c k := by
    calc
      (∑' n : ℤ, f n) = (∑' n : ℕ, q n) - f 0 := by rw [hnat]; ring
      _ = ((∑' k : ℕ, q (2 * k)) + ∑' k : ℕ, q (2 * k + 1)) - f 0 := by
        rw [hsplit]
      _ = 1 + 2 * ∑' k : ℕ, c k := by rw [heven, hodd, hf0]; ring
  have h29 := rvachev_even_translate_fourier F hF t
  have h29' : (rvachevUp F t : ℂ) = (2 : ℂ)⁻¹ * ∑' n : ℤ, f n := by
    rw [← Complex.ofReal_tsum,
      rvachev_even_translate_sum_eq_self F hF ht0 ht1] at h29
    simpa only [f] using h29
  calc
    (rvachevUp F t : ℂ) = (2 : ℂ)⁻¹ * ∑' n : ℤ, f n := h29'
    _ = (2 : ℂ)⁻¹ + ∑' k : ℕ, c k := by rw [hz]; ring
    _ = (2 : ℂ)⁻¹ +
        ∑' k : ℕ,
          rvachevFourier F (((((2 * k + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) *
            (Real.cos ((2 * k + 1) * Real.pi * t) : ℂ) := by
      apply congrArg ((2 : ℂ)⁻¹ + ·)
      apply tsum_congr
      intro k
      dsimp only [c]
      congr 2
      ring_nf

/-- Equation (31), Poisson summation specialized at `t = 0`. -/
theorem rvachev_poisson_at_zero
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ} (ha : 0 < a) :
    (∑' m : ℤ, (rvachevUp F (a * m) : ℂ)) =
      ∑' m : ℤ, ((a⁻¹ : ℝ) : ℂ) *
        rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) := by
  simpa using rvachev_poisson_summation F hF ha 0

/-- Poisson summation at zero for an arbitrary nonzero lattice spacing.
The covolume is the absolute value of the spacing; changing its sign leaves
the even spatial density and Fourier transform unchanged. -/
theorem rvachev_poisson_at_zero_of_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ} (ha : a ≠ 0) :
    (∑' m : ℤ, (rvachevUp F (a * m) : ℂ)) =
      ∑' m : ℤ, (((|a|)⁻¹ : ℝ) : ℂ) *
        rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) := by
  by_cases ha_pos : 0 < a
  · simpa [abs_of_pos ha_pos] using rvachev_poisson_at_zero F hF ha_pos
  · have ha_neg : a < 0 :=
      lt_of_le_of_ne (le_of_not_gt ha_pos) ha
    calc
      (∑' m : ℤ, (rvachevUp F (a * m) : ℂ)) =
          ∑' m : ℤ, (rvachevUp F ((-a) * m) : ℂ) := by
        apply tsum_congr
        intro m
        have harg : a * (m : ℝ) = -((-a) * (m : ℝ)) := by ring
        rw [harg, rvachev_even F hF]
      _ = ∑' m : ℤ, (((-a)⁻¹ : ℝ) : ℂ) *
          rvachevFourier F ((((m : ℝ) / (-a) : ℝ) : ℂ)) :=
        rvachev_poisson_at_zero F hF (neg_pos.mpr ha_neg)
      _ = ∑' m : ℤ, (((|a|)⁻¹ : ℝ) : ℂ) *
          rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) := by
        apply tsum_congr
        intro m
        rw [abs_of_neg ha_neg]
        have harg : ((((m : ℝ) / (-a) : ℝ) : ℂ)) =
            -((((m : ℝ) / a : ℝ) : ℂ)) := by
          push_cast
          field_simp [ha]
        rw [harg, rvachevFourier_neg F hF]

/-- Once the lattice spacing is at least `1 / 2`, compact support leaves only
the central term and the two nearest neighbors. -/
theorem rvachev_lattice_sum_of_one_half_le
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ}
    (ha0 : 1 / 2 ≤ a) :
    ∑' m : ℤ, rvachevUp F (a * m) = 1 + 2 * rvachevUp F a := by
  rw [tsum_eq_sum (s := {(-1 : ℤ), 0, 1})]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        rw [show a * (-1 : ℤ) = -a by push_cast; ring,
          (rvachev_even F hF a)]
        simp only [Int.cast_zero, mul_zero, Int.cast_one, mul_one,
          rvachevUp_zero F hF]
        ring
      · simp
    · simp
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    rcases (show m ≤ -2 ∨ 2 ≤ m by omega) with hmneg | hmpos
    · rw [rvachevUp_eq_zero_of_le_neg_one F hF]
      have hmnegR : (m : ℝ) ≤ -2 := by exact_mod_cast hmneg
      nlinarith
    · rw [rvachevUp_eq_zero_of_one_le F hF]
      have hmposR : (2 : ℝ) ≤ m := by exact_mod_cast hmpos
      nlinarith

/-- Compact support reduces the lattice sum to three terms whenever the
magnitude of the spacing is at least one half.  This sign-invariant form is
the natural companion to `rvachev_poisson_at_zero_of_ne_zero`. -/
theorem rvachev_lattice_sum_of_one_half_le_abs
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ}
    (ha0 : 1 / 2 ≤ |a|) :
    ∑' m : ℤ, rvachevUp F (a * m) = 1 + 2 * rvachevUp F a := by
  by_cases ha_nonneg : 0 ≤ a
  · exact rvachev_lattice_sum_of_one_half_le F hF
      (a := a) (by simpa [abs_of_nonneg ha_nonneg] using ha0)
  · have ha_neg : a < 0 := lt_of_not_ge ha_nonneg
    have h := rvachev_lattice_sum_of_one_half_le F hF
      (a := -a) (by simpa [abs_of_neg ha_neg] using ha0)
    calc
      (∑' m : ℤ, rvachevUp F (a * m)) =
          ∑' m : ℤ, rvachevUp F ((-a) * m) := by
        apply tsum_congr
        intro m
        have harg : a * (m : ℝ) = -((-a) * (m : ℝ)) := by ring
        rw [harg, rvachev_even F hF]
      _ = 1 + 2 * rvachevUp F (-a) := h
      _ = 1 + 2 * rvachevUp F a := by rw [rvachev_even F hF]

/-- The support specialization of Poisson summation for either sign of the
lattice spacing.  The inverse covolume is governed by the absolute value,
while the dual frequencies retain the oriented spacing. -/
theorem rvachev_poisson_support_specialization_unscaled_of_one_half_le_abs
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ}
    (ha0 : 1 / 2 ≤ |a|) :
    (1 : ℂ) + 2 * rvachevUp F a =
      ∑' m : ℤ, (((|a|)⁻¹ : ℝ) : ℂ) *
        rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) := by
  have habs_pos : 0 < |a| :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) ha0
  have ha : a ≠ 0 := abs_pos.mp habs_pos
  rw [← rvachev_poisson_at_zero_of_ne_zero F hF ha,
    ← Complex.ofReal_tsum,
    rvachev_lattice_sum_of_one_half_le_abs F hF ha0]
  push_cast
  rfl

/-- Multiplying the sign-invariant support identity by the covolume removes
the inverse factor term by term. -/
theorem rvachev_poisson_support_specialization_of_one_half_le_abs
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ}
    (ha0 : 1 / 2 ≤ |a|) :
    ((|a| : ℝ) : ℂ) + 2 * ((|a| : ℝ) : ℂ) * rvachevUp F a =
      ∑' m : ℤ, rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) := by
  have habs_pos : 0 < |a| :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) ha0
  have ha_abs : |a| ≠ 0 := habs_pos.ne'
  have h :=
    rvachev_poisson_support_specialization_unscaled_of_one_half_le_abs
      F hF ha0
  calc
    ((|a| : ℝ) : ℂ) + 2 * ((|a| : ℝ) : ℂ) * rvachevUp F a =
        ((|a| : ℝ) : ℂ) * ((1 : ℂ) + 2 * rvachevUp F a) := by ring
    _ = ((|a| : ℝ) : ℂ) * ∑' m : ℤ, (((|a|)⁻¹ : ℝ) : ℂ) *
        rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) := by rw [h]
    _ = ∑' m : ℤ, rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      push_cast
      field_simp [ha_abs]

/-- The direct support specialization of (31), before multiplying by `a`,
for every lattice spacing `a ≥ 1 / 2`.

The paper states (31)--(32) under `1 / 2 ≤ a ≤ 1`, but the upper bound is
never needed: the two ingredients
`rvachev_poisson_at_zero` (which needs only `0 < a`, itself a consequence of
`1 / 2 ≤ a`) and `rvachev_lattice_sum_of_one_half_le` (which needs only
`1 / 2 ≤ a`) both hold on the whole ray.  This is the upper-bound-free companion
of `rvachev_poisson_support_specialization_unscaled`, which is kept with its
original signature for compatibility. -/
theorem rvachev_poisson_support_specialization_unscaled_of_one_half_le
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ}
    (ha0 : 1 / 2 ≤ a) :
    (1 : ℂ) + 2 * rvachevUp F a =
      ∑' m : ℤ, ((a⁻¹ : ℝ) : ℂ) *
        rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) := by
  have ha_nonneg : 0 ≤ a :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) ha0
  simpa [abs_of_nonneg ha_nonneg] using
    (rvachev_poisson_support_specialization_unscaled_of_one_half_le_abs
      F hF (a := a) (by simpa [abs_of_nonneg ha_nonneg] using ha0))

/-- Corrected equation (32) for every lattice spacing `a ≥ 1 / 2`.

As above, the paper's upper bound `a ≤ 1` plays no role; multiplying the
unscaled identity by `a` only needs `a ≠ 0`.  The source also leaves an extra
factor `1 / a` on the right after that multiplication, which is corrected
here.  This is the upper-bound-free companion of
`rvachev_poisson_support_specialization`, which is kept with its original
signature for compatibility. -/
theorem rvachev_poisson_support_specialization_of_one_half_le
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ}
    (ha0 : 1 / 2 ≤ a) :
    (a : ℂ) + 2 * (a : ℂ) * rvachevUp F a =
      ∑' m : ℤ, rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) := by
  have ha_nonneg : 0 ≤ a :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) ha0
  simpa [abs_of_nonneg ha_nonneg] using
    (rvachev_poisson_support_specialization_of_one_half_le_abs
      F hF (a := a) (by simpa [abs_of_nonneg ha_nonneg] using ha0))

set_option linter.unusedVariables false in
/-- The direct support specialization of (31), before multiplying by `a`.
This is the identity from which the corrected equation (32) follows.

Kept for compatibility with the paper's hypotheses; the upper bound `a ≤ 1`
is not needed, see
`rvachev_poisson_support_specialization_unscaled_of_one_half_le`. -/
theorem rvachev_poisson_support_specialization_unscaled
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ}
    (ha0 : 1 / 2 ≤ a) (ha1 : a ≤ 1) :
    (1 : ℂ) + 2 * rvachevUp F a =
      ∑' m : ℤ, ((a⁻¹ : ℝ) : ℂ) *
        rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) :=
  rvachev_poisson_support_specialization_unscaled_of_one_half_le F hF ha0

set_option linter.unusedVariables false in
/-- Corrected equation (32).  The source leaves an extra factor `1 / a` on
the right after multiplying the preceding identity by `a`.

Kept for compatibility with the paper's hypotheses; the upper bound `a ≤ 1`
is not needed, see `rvachev_poisson_support_specialization_of_one_half_le`. -/
theorem rvachev_poisson_support_specialization
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ}
    (ha0 : 1 / 2 ≤ a) (ha1 : a ≤ 1) :
    (a : ℂ) + 2 * (a : ℂ) * rvachevUp F a =
      ∑' m : ℤ, rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ)) :=
  rvachev_poisson_support_specialization_of_one_half_le F hF ha0

end

end Fabius
