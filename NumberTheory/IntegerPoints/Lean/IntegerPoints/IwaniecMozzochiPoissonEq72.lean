import IntegerPoints.IwaniecMozzochi
import IntegerPoints.Poisson
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries

/-!
# Iwaniec--Mozzochi (7.2): Poisson summation for the trapezoid weight

The only slightly delicate point in this application of Poisson summation is
absolute convergence on the Fourier side.  Compact support is enough for the
lattice sum, but it is *not* by itself enough for summability of the sampled
Fourier transform.

Here the trapezoid is split into its two affine ramps and its constant middle
piece.  One integration by parts on each piece writes every nonzero Fourier
sample as `1 / n` times three Fourier coefficients of continuous derivative
pieces.  Parseval makes each of those coefficient sequences square summable;
Cauchy--Schwarz (in the elementary `uv <= u^2 + v^2` form) against
`(1 / |n|)` proves absolute summability.  This also records explicitly why the
corners of the trapezoid cause no problem.

With Mathlib's convention `F f(n) = integral e(-n l) f(l) dl`, applying
Poisson to `omega(l) e(r(l) - ahl/c)` produces the index
`k = -ah - cn`.  The final reindexing is therefore the explicit equivalence
between `Z` and the congruence class `k == -ah (mod c)`.
-/

open scoped BigOperators FourierTransform
open Real Set Filter intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace IwaniecMozzochiEq72

/-! ### The smooth phase on the support -/

private noncomputable def shiftedPhase
    (x m v : ℝ) (a c h : ℕ) (l : ℝ) : ℝ :=
  -((a : ℝ) * h * l / c) + rPhase x h m v l

private noncomputable def oscillatoryFactor
    (x m v : ℝ) (a c h : ℕ) (l : ℝ) : ℂ :=
  e (shiftedPhase x m v a c h l)

private noncomputable def oscillatoryFactorDeriv
    (x m v : ℝ) (a c h : ℕ) (l : ℝ) : ℂ :=
  2 * π * Complex.I * deriv (shiftedPhase x m v a c h) l *
    oscillatoryFactor x m v a c h l

private theorem shiftedPhase_contDiffOn
    (x m v : ℝ) (a c h : ℕ) (hm : 0 < m) (hv : 0 ≤ v) (hc : 0 < c) :
    ContDiffOn ℝ 1 (shiftedPhase x m v a c h) (Ioi (-m)) := by
  have hm0 : m ≠ 0 := hm.ne'
  have hmv0 : m + v ≠ 0 := by positivity
  have hc0 : (c : ℝ) ≠ 0 := by positivity
  unfold shiftedPhase rPhase
  fun_prop (disch := first | positivity | grind [Set.mem_Ioi])

private theorem oscillatoryFactor_hasDerivAt
    (x m v : ℝ) (a c h : ℕ) (hm : 0 < m) (hv : 0 ≤ v) (hc : 0 < c)
    {l : ℝ} (hl : -m < l) :
    HasDerivAt (oscillatoryFactor x m v a c h)
      (oscillatoryFactorDeriv x m v a c h l) l := by
  unfold oscillatoryFactorDeriv oscillatoryFactor
  exact PS.hasDerivAt_e_comp
    ((((shiftedPhase_contDiffOn x m v a c h hm hv hc).differentiableOn one_ne_zero)
      l hl).differentiableAt (Ioi_mem_nhds hl)).hasDerivAt

private theorem oscillatoryFactor_continuousOn
    (x m v : ℝ) (a c h : ℕ) (hm : 0 < m) (hv : 0 ≤ v) (hc : 0 < c) :
    ContinuousOn (oscillatoryFactor x m v a c h) (Ioi (-m)) := by
  intro l hl
  exact (oscillatoryFactor_hasDerivAt x m v a c h hm hv hc hl).continuousAt.continuousWithinAt

private theorem oscillatoryFactorDeriv_continuousOn
    (x m v : ℝ) (a c h : ℕ) (hm : 0 < m) (hv : 0 ≤ v) (hc : 0 < c) :
    ContinuousOn (oscillatoryFactorDeriv x m v a c h) (Ioi (-m)) := by
  have hphaseDeriv : ContinuousOn (deriv (shiftedPhase x m v a c h)) (Ioi (-m)) :=
    (shiftedPhase_contDiffOn x m v a c h hm hv hc).continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl
  unfold oscillatoryFactorDeriv
  exact ((continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hphaseDeriv)).mul
    (oscillatoryFactor_continuousOn x m v a c h hm hv hc))

/-! ### Elementary facts about the trapezoid -/

private theorem trapezoid_eq_zero_of_le {L₁ L₂ l : ℝ} (hl : l ≤ L₁ - 1) :
    trapezoid L₁ L₂ l = 0 := by
  unfold trapezoid
  rw [max_eq_left]
  linarith [min_le_left (l - L₁) (min (L₂ - l) 0)]

private theorem trapezoid_eq_zero_of_ge {L₁ L₂ l : ℝ} (hl : L₂ + 1 ≤ l) :
    trapezoid L₁ L₂ l = 0 := by
  unfold trapezoid
  rw [max_eq_left]
  have hmin : min (l - L₁) (min (L₂ - l) 0) ≤ L₂ - l :=
    (min_le_right _ _).trans (min_le_left _ _)
  linarith

private theorem trapezoid_eq_leftRamp {L₁ L₂ l : ℝ}
    (h12 : L₁ < L₂) (hl0 : L₁ - 1 ≤ l) (hl1 : l ≤ L₁) :
    trapezoid L₁ L₂ l = l - (L₁ - 1) := by
  unfold trapezoid
  rw [min_eq_right (by linarith : 0 ≤ L₂ - l)]
  rw [min_eq_left (by linarith : l - L₁ ≤ 0)]
  rw [max_eq_right (by linarith : 0 ≤ 1 + (l - L₁))]
  ring

private theorem trapezoid_eq_one {L₁ L₂ l : ℝ}
    (hl1 : L₁ ≤ l) (hl2 : l ≤ L₂) :
    trapezoid L₁ L₂ l = 1 := by
  unfold trapezoid
  rw [min_eq_right (by linarith : 0 ≤ L₂ - l)]
  rw [min_eq_right (by linarith : 0 ≤ l - L₁)]
  simp

private theorem trapezoid_eq_rightRamp {L₁ L₂ l : ℝ}
    (h12 : L₁ < L₂) (hl2 : L₂ ≤ l) (hl3 : l ≤ L₂ + 1) :
    trapezoid L₁ L₂ l = (L₂ + 1) - l := by
  unfold trapezoid
  rw [min_eq_left (by linarith : L₂ - l ≤ 0)]
  rw [min_eq_right (by linarith : L₂ - l ≤ l - L₁)]
  rw [max_eq_right (by linarith : 0 ≤ 1 + (L₂ - l))]
  ring

private theorem continuous_trapezoid (L₁ L₂ : ℝ) :
    Continuous (trapezoid L₁ L₂) := by
  unfold trapezoid
  fun_prop

/-! ### A Parseval-based summability lemma for one interval -/

private theorem memLp_two_Ioc_of_continuousOn {g : ℝ → ℂ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    MemLp g 2 (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  apply MemLp.of_bound
    ((hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun l hl => hC l ⟨hl.1.le, hl.2⟩

/-- The integral over an interval with integral endpoints, encoded as a
Fourier coefficient on the circle whose period is the interval length. -/
private noncomputable def pieceFourier {p q : ℤ} (hpq : p < q)
    (g : ℝ → ℂ) (n : ℤ) : ℂ :=
  (((q - p : ℤ) : ℝ) : ℂ) *
    fourierCoeffOn (by exact_mod_cast hpq : (p : ℝ) < q) g (n * (q - p))

private theorem fourier_piece_kernel {p q n : ℤ} (hpq : p < q) (l : ℝ) :
    fourier (-(n * (q - p)))
        (l : AddCircle ((q : ℝ) - (p : ℝ))) = e (-((n : ℝ) * l)) := by
  have hd : (q : ℝ) - (p : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hpq.ne')
  have hquot :
      ((-(n * (q - p)) : ℤ) : ℝ) * l / ((q : ℝ) - (p : ℝ)) =
        -((n : ℝ) * l) := by
    apply (div_eq_iff hd).2
    push_cast
    ring
  have hquotC :
      (((( -(n * (q - p)) : ℤ) : ℝ) : ℂ) * (l : ℂ)) /
          (((q : ℝ) - (p : ℝ) : ℝ) : ℂ) =
        ((-((n : ℝ) * l) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg] using
      congrArg (fun t : ℝ => (t : ℂ)) hquot
  rw [fourier_coe_apply]
  unfold e
  congr 1
  calc
    _ = 2 * π * Complex.I *
        (((( -(n * (q - p)) : ℤ) : ℝ) : ℂ) * (l : ℂ) /
          (((q : ℝ) - (p : ℝ) : ℝ) : ℂ)) := by
      simp only [Complex.ofReal_intCast, div_eq_mul_inv, mul_assoc]
    _ = _ := by rw [hquotC]

private theorem real_fourier_kernel_eq_e (n : ℤ) (l : ℝ) :
    Complex.exp ((-2 * π * l * (n : ℝ) : ℝ) * Complex.I) =
      e (-((n : ℝ) * l)) := by
  unfold e
  congr 1
  push_cast
  ring

private theorem pieceFourier_eq_integral {p q : ℤ} (hpq : p < q)
    (g : ℝ → ℂ) (n : ℤ) :
    pieceFourier hpq g n =
      ∫ l in (p : ℝ)..(q : ℝ), e (-((n : ℝ) * l)) * g l := by
  unfold pieceFourier
  rw [fourierCoeffOn_eq_integral]
  simp_rw [fourier_piece_kernel hpq]
  simp only [smul_eq_mul, Complex.real_smul]
  have hd : ((q - p : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hpq.ne')
  have hden : (q : ℂ) - (p : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hpq.ne')
  push_cast
  calc
    _ = ((q : ℂ) - (p : ℂ)) *
        (∫ l in (p : ℝ)..(q : ℝ), e (-((n : ℝ) * l)) * g l) /
          ((q : ℂ) - (p : ℂ)) := by ring
    _ = _ := mul_div_cancel_left₀ _ hden

/-- One integration by parts on a piece.  The integral endpoints make the
boundary character equal to one, and make the interval-length factor cancel
from the denominator. -/
private theorem pieceFourier_parts {p q : ℤ} (hpq : p < q)
    {F F' : ℝ → ℂ} (n : ℤ) (hn : n ≠ 0)
    (hF : ContinuousOn F (Icc (p : ℝ) (q : ℝ)))
    (hFF' : ∀ l, l ∈ Ioo (p : ℝ) (q : ℝ) → HasDerivAt F (F' l) l)
    (hF'i : IntervalIntegrable F' volume (p : ℝ) (q : ℝ)) :
    pieceFourier hpq F n =
      (1 / (-2 * π * Complex.I * (n : ℂ))) *
        ((F q - F p) - pieceFourier hpq F' n) := by
  have hab : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq.ne'
  have hN : n * (q - p) ≠ 0 := mul_ne_zero hn hd
  unfold pieceFourier
  rw [fourierCoeffOn_of_hasDerivAt_Ioo hab hN
    (by simpa [uIcc_of_le hab.le] using hF)
    (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hFF') hF'i]
  rw [fourier_piece_kernel hpq]
  have hboundary : e (-((n : ℝ) * (p : ℝ))) = 1 := by
    have heq : -((n : ℝ) * (p : ℝ)) = ((-n * p : ℤ) : ℝ) := by push_cast; ring
    rw [heq, KL.e_int]
  rw [hboundary, one_mul]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hdC : (((q - p : ℤ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  have hden : (q : ℂ) - (p : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hpq.ne')
  push_cast
  field_simp [hnC, hden, Real.pi_ne_zero, Complex.I_ne_zero]

private theorem summable_pieceFourier_norm_sq {p q : ℤ} (hpq : p < q)
    {g : ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (Ioc (p : ℝ) (q : ℝ)))) :
    Summable fun n : ℤ => ‖pieceFourier hpq g n‖ ^ 2 := by
  have hab : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hs : Summable fun n : ℤ => ‖fourierCoeffOn hab g n‖ ^ 2 :=
    (hasSum_sq_fourierCoeffOn hab hg).summable
  have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq.ne'
  have hinj : Function.Injective (fun n : ℤ => n * (q - p)) := by
    intro i j hij
    exact mul_right_cancel₀ hd hij
  have hs' := hs.comp_injective hinj
  have hlen : 0 < ((q - p : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hpq
  refine (hs'.mul_left (((q - p : ℤ) : ℝ) ^ 2)).congr fun n => ?_
  simp only [pieceFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos hlen]
  simp only [Function.comp_apply]
  ring

private theorem summable_one_div_abs_mul_norm {J : ℤ → ℂ}
    (hJ : Summable fun n : ℤ => ‖J n‖ ^ 2) :
    Summable fun n : ℤ => (1 / |(n : ℝ)|) * ‖J n‖ := by
  have hinv : Summable fun n : ℤ => 1 / (n : ℝ) ^ (2 : ℕ) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hinv' : Summable fun n : ℤ => (1 / |(n : ℝ)|) ^ 2 :=
    hinv.congr fun n => by
      rw [div_pow, one_pow, sq_abs]
  exact (hinv'.add hJ).of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (norm_nonneg _)) fun n => by
      have hu : 0 ≤ 1 / |(n : ℝ)| := by positivity
      have hv : 0 ≤ ‖J n‖ := norm_nonneg _
      nlinarith [sq_nonneg (1 / |(n : ℝ)| - ‖J n‖)]

/-! ### Three pieces imply summability of the sampled Fourier transform -/

private theorem summable_of_three_piece_parts
    {p₀ p₁ p₂ p₃ : ℤ}
    (h01 : p₀ < p₁) (h12 : p₁ < p₂) (h23 : p₂ < p₃)
    {F₀ F₁ F₂ F₀' F₁' F₂' : ℝ → ℂ} {FT : ℤ → ℂ}
    (hF₀ : ContinuousOn F₀ (Icc (p₀ : ℝ) (p₁ : ℝ)))
    (hF₁ : ContinuousOn F₁ (Icc (p₁ : ℝ) (p₂ : ℝ)))
    (hF₂ : ContinuousOn F₂ (Icc (p₂ : ℝ) (p₃ : ℝ)))
    (hd₀ : ∀ l, l ∈ Ioo (p₀ : ℝ) (p₁ : ℝ) → HasDerivAt F₀ (F₀' l) l)
    (hd₁ : ∀ l, l ∈ Ioo (p₁ : ℝ) (p₂ : ℝ) → HasDerivAt F₁ (F₁' l) l)
    (hd₂ : ∀ l, l ∈ Ioo (p₂ : ℝ) (p₃ : ℝ) → HasDerivAt F₂ (F₂' l) l)
    (hi₀ : IntervalIntegrable F₀' volume (p₀ : ℝ) (p₁ : ℝ))
    (hi₁ : IntervalIntegrable F₁' volume (p₁ : ℝ) (p₂ : ℝ))
    (hi₂ : IntervalIntegrable F₂' volume (p₂ : ℝ) (p₃ : ℝ))
    (hL2₀ : MemLp F₀' 2 (volume.restrict (Ioc (p₀ : ℝ) (p₁ : ℝ))))
    (hL2₁ : MemLp F₁' 2 (volume.restrict (Ioc (p₁ : ℝ) (p₂ : ℝ))))
    (hL2₂ : MemLp F₂' 2 (volume.restrict (Ioc (p₂ : ℝ) (p₃ : ℝ))))
    (hboundary :
      (F₀ p₁ - F₀ p₀) + (F₁ p₂ - F₁ p₁) + (F₂ p₃ - F₂ p₂) = 0)
    (hFT : ∀ n, FT n =
      pieceFourier h01 F₀ n + pieceFourier h12 F₁ n + pieceFourier h23 F₂ n) :
    Summable FT := by
  let J₀ : ℤ → ℂ := fun n => pieceFourier h01 F₀' n
  let J₁ : ℤ → ℂ := fun n => pieceFourier h12 F₁' n
  let J₂ : ℤ → ℂ := fun n => pieceFourier h23 F₂' n
  have hJ₀sq : Summable fun n : ℤ => ‖J₀ n‖ ^ 2 := by
    simpa [J₀] using summable_pieceFourier_norm_sq h01 hL2₀
  have hJ₁sq : Summable fun n : ℤ => ‖J₁ n‖ ^ 2 := by
    simpa [J₁] using summable_pieceFourier_norm_sq h12 hL2₁
  have hJ₂sq : Summable fun n : ℤ => ‖J₂ n‖ ^ 2 := by
    simpa [J₂] using summable_pieceFourier_norm_sq h23 hL2₂
  have hJ₀ := summable_one_div_abs_mul_norm hJ₀sq
  have hJ₁ := summable_one_div_abs_mul_norm hJ₁sq
  have hJ₂ := summable_one_div_abs_mul_norm hJ₂sq
  let C : ℝ := ‖(1 / (-2 * π * Complex.I) : ℂ)‖
  let tail : ℤ → ℝ := fun n => C *
    ((1 / |(n : ℝ)|) * ‖J₀ n‖ +
      (1 / |(n : ℝ)|) * ‖J₁ n‖ +
      (1 / |(n : ℝ)|) * ‖J₂ n‖)
  have htail : Summable tail := by
    exact ((hJ₀.add hJ₁).add hJ₂).mul_left C
  let delta : ℤ → ℝ := fun n => if n = 0 then ‖FT 0‖ else 0
  have hdelta : Summable delta := by
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton 0).subset (by simp [delta, Function.support])
  have hparts₀ (n : ℤ) (hn : n ≠ 0) :
      pieceFourier h01 F₀ n =
        (1 / (-2 * π * Complex.I * (n : ℂ))) *
          ((F₀ p₁ - F₀ p₀) - J₀ n) := by
    simpa [J₀] using pieceFourier_parts h01 n hn hF₀ hd₀ hi₀
  have hparts₁ (n : ℤ) (hn : n ≠ 0) :
      pieceFourier h12 F₁ n =
        (1 / (-2 * π * Complex.I * (n : ℂ))) *
          ((F₁ p₂ - F₁ p₁) - J₁ n) := by
    simpa [J₁] using pieceFourier_parts h12 n hn hF₁ hd₁ hi₁
  have hparts₂ (n : ℤ) (hn : n ≠ 0) :
      pieceFourier h23 F₂ n =
        (1 / (-2 * π * Complex.I * (n : ℂ))) *
          ((F₂ p₃ - F₂ p₂) - J₂ n) := by
    simpa [J₂] using pieceFourier_parts h23 n hn hF₂ hd₂ hi₂
  have hformula (n : ℤ) (hn : n ≠ 0) :
      FT n = -(1 / (-2 * π * Complex.I * (n : ℂ))) * (J₀ n + J₁ n + J₂ n) := by
    rw [hFT n, hparts₀ n hn, hparts₁ n hn, hparts₂ n hn]
    calc
      _ = (1 / (-2 * π * Complex.I * (n : ℂ))) *
          (((F₀ p₁ - F₀ p₀) + (F₁ p₂ - F₁ p₁) +
              (F₂ p₃ - F₂ p₂)) -
            (J₀ n + J₁ n + J₂ n)) := by
              ring
      _ = _ := by
        rw [hboundary]
        ring
  have hinvnorm (n : ℤ) (hn : n ≠ 0) :
      ‖(1 / (-2 * π * Complex.I * (n : ℂ)) : ℂ)‖ =
        C * (1 / |(n : ℝ)|) := by
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hbase : (-2 * π * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero
    rw [show (1 / (-2 * π * Complex.I * (n : ℂ)) : ℂ) =
        (1 / (-2 * π * Complex.I)) * (1 / (n : ℂ)) by
          field_simp [hnC, hbase]]
    rw [norm_mul]
    simp [C, norm_div, Real.norm_eq_abs]
  refine Summable.of_norm <| (hdelta.add htail).of_nonneg_of_le
    (fun n => norm_nonneg (FT n)) fun n => ?_
  by_cases hn : n = 0
  · subst n
    simp [delta, tail]
  · rw [hformula n hn, norm_mul, norm_neg, hinvnorm n hn]
    simp only [delta, hn, if_false, zero_add, tail]
    have htri : ‖J₀ n + J₁ n + J₂ n‖ ≤ ‖J₀ n‖ + ‖J₁ n‖ + ‖J₂ n‖ := by
      calc
        ‖J₀ n + J₁ n + J₂ n‖ ≤ ‖J₀ n + J₁ n‖ + ‖J₂ n‖ := norm_add_le _ _
        _ ≤ (‖J₀ n‖ + ‖J₁ n‖) + ‖J₂ n‖ := by gcongr; exact norm_add_le _ _
    have hC : 0 ≤ C := norm_nonneg _
    have hu : 0 ≤ 1 / |(n : ℝ)| := by positivity
    calc
      C * (1 / |(n : ℝ)|) * ‖J₀ n + J₁ n + J₂ n‖
          ≤ C * (1 / |(n : ℝ)|) * (‖J₀ n‖ + ‖J₁ n‖ + ‖J₂ n‖) := by
            gcongr
      _ = C * ((1 / |(n : ℝ)|) * ‖J₀ n‖ +
          (1 / |(n : ℝ)|) * ‖J₁ n‖ +
          (1 / |(n : ℝ)|) * ‖J₂ n‖) := by ring

/-! ### Congruence-class reindexing -/

/-- `n |-> r - cn` parametrizes, without repetition, the residue class of
`r` modulo a nonzero integer `c`. -/
private def residueClassEquiv (r c : ℤ) (hc : c ≠ 0) :
    ℤ ≃ {k : ℤ // k ≡ r [ZMOD c]} where
  toFun n := ⟨r - c * n, by
    rw [Int.modEq_iff_dvd]
    use n
    ring⟩
  invFun k := (r - k.1) / c
  left_inv n := by
    dsimp
    rw [show r - (r - c * n) = c * n by ring, Int.mul_ediv_cancel_left n hc]
  right_inv k := by
    apply Subtype.ext
    rcases Int.modEq_iff_add_fac.mp k.2.symm with ⟨t, ht⟩
    dsimp
    rw [ht, show r - (r + c * t) = c * (-t) by ring,
      Int.mul_ediv_cancel_left (-t) hc]
    ring

private theorem tsum_residueClass (g : ℤ → ℂ) (r c : ℤ) (hc : c ≠ 0) :
    (∑' n : ℤ, g (r - c * n)) =
      ∑' k : ℤ, if k ≡ r [ZMOD c] then g k else 0 := by
  calc
    (∑' n : ℤ, g (r - c * n)) =
        ∑' k : {k : ℤ // k ≡ r [ZMOD c]}, g k.1 := by
          simpa [residueClassEquiv] using
            (residueClassEquiv r c hc).tsum_eq (fun k => g k.1)
    _ = ∑' k : ℤ, Set.indicator {k : ℤ | k ≡ r [ZMOD c]} g k :=
      tsum_subtype {k : ℤ | k ≡ r [ZMOD c]} g
    _ = ∑' k : ℤ, if k ≡ r [ZMOD c] then g k else 0 := by
      apply tsum_congr
      intro k
      by_cases hk : k ≡ r [ZMOD c] <;> simp [Set.indicator, hk]

end IwaniecMozzochiEq72

open IwaniecMozzochiEq72

/-- **Iwaniec--Mozzochi (7.2).**  Poisson summation for the compactly
supported trapezoid, with Mathlib's Fourier-sign convention reindexed as the
congruence class `k == -ah (mod c)`. -/
theorem iwaniecMozzochi_eq72_holds : iwaniecMozzochi_eq72 := by
  rw [iwaniecMozzochi_eq72]
  intro x m v a c h L₁ L₂ hx hh hm hv hv1 hc h12 hmL
  have hcPos : 0 < c := Nat.zero_lt_one.trans_le hc
  have hcR : (0 : ℝ) < c := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hc)
  have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hc))
  have h01 : L₁ - 1 < L₁ := by omega
  have h23 : L₂ < L₂ + 1 := by omega
  have h01R : (((L₁ - 1 : ℤ) : ℝ)) < (L₁ : ℝ) := by exact_mod_cast h01
  have h23R : (L₂ : ℝ) < (((L₂ + 1 : ℤ) : ℝ)) := by exact_mod_cast h23
  have h12R : (L₁ : ℝ) < L₂ := by exact_mod_cast h12
  have hA : -m < ((L₁ - 1 : ℤ) : ℝ) := by
    push_cast
    exact hmL
  have hsafe :
      Icc (((L₁ - 1 : ℤ) : ℝ)) (((L₂ + 1 : ℤ) : ℝ)) ⊆ Ioi (-m) := by
    intro l hl
    exact hA.trans_le hl.1

  let q : ℝ → ℂ := oscillatoryFactor x m v a c h
  let q' : ℝ → ℂ := oscillatoryFactorDeriv x m v a c h
  let F₀ : ℝ → ℂ := fun l =>
    ((l - (((L₁ - 1 : ℤ) : ℝ)) : ℝ) : ℂ) * q l
  let F₁ : ℝ → ℂ := q
  let F₂ : ℝ → ℂ := fun l =>
    (((((L₂ + 1 : ℤ) : ℝ)) - l : ℝ) : ℂ) * q l
  let F₀' : ℝ → ℂ := fun l =>
    q l + ((l - (((L₁ - 1 : ℤ) : ℝ)) : ℝ) : ℂ) * q' l
  let F₁' : ℝ → ℂ := q'
  let F₂' : ℝ → ℂ := fun l =>
    -q l + (((((L₂ + 1 : ℤ) : ℝ)) - l : ℝ) : ℂ) * q' l

  have hq : ContinuousOn q
      (Icc (((L₁ - 1 : ℤ) : ℝ)) (((L₂ + 1 : ℤ) : ℝ))) :=
    (oscillatoryFactor_continuousOn x m v a c h hm hv hcPos).mono hsafe
  have hq' : ContinuousOn q'
      (Icc (((L₁ - 1 : ℤ) : ℝ)) (((L₂ + 1 : ℤ) : ℝ))) :=
    (oscillatoryFactorDeriv_continuousOn x m v a c h hm hv hcPos).mono hsafe

  have hseg₀ : Icc (((L₁ - 1 : ℤ) : ℝ)) (L₁ : ℝ) ⊆
      Icc (((L₁ - 1 : ℤ) : ℝ)) (((L₂ + 1 : ℤ) : ℝ)) := by
    intro l hl
    exact ⟨hl.1, hl.2.trans (h12R.trans h23R).le⟩
  have hseg₁ : Icc (L₁ : ℝ) (L₂ : ℝ) ⊆
      Icc (((L₁ - 1 : ℤ) : ℝ)) (((L₂ + 1 : ℤ) : ℝ)) := by
    intro l hl
    constructor
    · exact h01R.le.trans hl.1
    · exact hl.2.trans h23R.le
  have hseg₂ : Icc (L₂ : ℝ) (((L₂ + 1 : ℤ) : ℝ)) ⊆
      Icc (((L₁ - 1 : ℤ) : ℝ)) (((L₂ + 1 : ℤ) : ℝ)) := by
    intro l hl
    exact ⟨(h01R.trans h12R).le.trans hl.1, hl.2⟩

  have hF₀ : ContinuousOn F₀ (Icc (((L₁ - 1 : ℤ) : ℝ)) (L₁ : ℝ)) := by
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.sub continuousOn_const)).mul (hq.mono hseg₀)
  have hF₁ : ContinuousOn F₁ (Icc (L₁ : ℝ) (L₂ : ℝ)) := hq.mono hseg₁
  have hF₂ : ContinuousOn F₂ (Icc (L₂ : ℝ) (((L₂ + 1 : ℤ) : ℝ))) := by
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.sub continuousOn_id)).mul (hq.mono hseg₂)
  have hF₀' : ContinuousOn F₀' (Icc (((L₁ - 1 : ℤ) : ℝ)) (L₁ : ℝ)) := by
    exact (hq.mono hseg₀).add <|
      (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_id.sub continuousOn_const)).mul (hq'.mono hseg₀)
  have hF₁' : ContinuousOn F₁' (Icc (L₁ : ℝ) (L₂ : ℝ)) := hq'.mono hseg₁
  have hF₂' : ContinuousOn F₂' (Icc (L₂ : ℝ) (((L₂ + 1 : ℤ) : ℝ))) := by
    exact (hq.mono hseg₂).neg.add <|
      (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.sub continuousOn_id)).mul (hq'.mono hseg₂)

  have hd₀ : ∀ l, l ∈ Ioo (((L₁ - 1 : ℤ) : ℝ)) (L₁ : ℝ) →
      HasDerivAt F₀ (F₀' l) l := by
    intro l hl
    have hqd := oscillatoryFactor_hasDerivAt x m v a c h hm hv hcPos
      (hA.trans hl.1)
    have hw : HasDerivAt
        (fun y : ℝ => ((y - (((L₁ - 1 : ℤ) : ℝ)) : ℝ) : ℂ)) 1 l :=
      ((hasDerivAt_id l).sub_const _).ofReal_comp
    convert! hw.mul hqd using 1 <;> simp [F₀, F₀', q, q']
  have hd₁ : ∀ l, l ∈ Ioo (L₁ : ℝ) (L₂ : ℝ) →
      HasDerivAt F₁ (F₁' l) l := by
    intro l hl
    simpa [F₁, F₁', q, q'] using
      oscillatoryFactor_hasDerivAt x m v a c h hm hv hcPos
        (hA.trans <| h01R.trans hl.1)
  have hd₂ : ∀ l, l ∈ Ioo (L₂ : ℝ) (((L₂ + 1 : ℤ) : ℝ)) →
      HasDerivAt F₂ (F₂' l) l := by
    intro l hl
    have hqd := oscillatoryFactor_hasDerivAt x m v a c h hm hv hcPos
      (hA.trans <| (h01R.trans h12R).trans hl.1)
    have hw : HasDerivAt
        (fun y : ℝ => (((((L₂ + 1 : ℤ) : ℝ)) - y : ℝ) : ℂ)) (-1) l := by
      convert! (((hasDerivAt_const l (((L₂ + 1 : ℤ) : ℝ))).sub
        (hasDerivAt_id l)).ofReal_comp) using 1 <;> norm_num
    convert! hw.mul hqd using 1 <;> simp [F₂, F₂', q, q']

  have hi₀ : IntervalIntegrable F₀' volume (((L₁ - 1 : ℤ) : ℝ)) (L₁ : ℝ) :=
    hF₀'.intervalIntegrable_of_Icc h01R.le
  have hi₁ : IntervalIntegrable F₁' volume (L₁ : ℝ) (L₂ : ℝ) :=
    hF₁'.intervalIntegrable_of_Icc h12R.le
  have hi₂ : IntervalIntegrable F₂' volume (L₂ : ℝ) (((L₂ + 1 : ℤ) : ℝ)) :=
    hF₂'.intervalIntegrable_of_Icc h23R.le
  have hL2₀ : MemLp F₀' 2
      (volume.restrict (Ioc (((L₁ - 1 : ℤ) : ℝ)) (L₁ : ℝ))) :=
    memLp_two_Ioc_of_continuousOn hF₀'
  have hL2₁ : MemLp F₁' 2 (volume.restrict (Ioc (L₁ : ℝ) (L₂ : ℝ))) :=
    memLp_two_Ioc_of_continuousOn hF₁'
  have hL2₂ : MemLp F₂' 2
      (volume.restrict (Ioc (L₂ : ℝ) (((L₂ + 1 : ℤ) : ℝ)))) :=
    memLp_two_Ioc_of_continuousOn hF₂'
  have hboundary :
      (F₀ (L₁ : ℝ) - F₀ (((L₁ - 1 : ℤ) : ℝ))) +
          (F₁ (L₂ : ℝ) - F₁ (L₁ : ℝ)) +
        (F₂ (((L₂ + 1 : ℤ) : ℝ)) - F₂ (L₂ : ℝ)) = 0 := by
    simp [F₀, F₁, F₂]

  let f : ℝ → ℂ := fun l => (trapezoid L₁ L₂ l : ℂ) * q l
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro l
    by_cases hl : l < ((L₁ - 1 : ℤ) : ℝ)
    · apply (continuousAt_const (x := l) (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hl] with y hy
      have hz : trapezoid (L₁ : ℝ) (L₂ : ℝ) y = 0 :=
        trapezoid_eq_zero_of_le (by
          have hy' : y < ((L₁ - 1 : ℤ) : ℝ) := hy
          simpa only [Int.cast_sub, Int.cast_one] using hy'.le)
      simp [f, hz]
    · have hsafe_l : -m < l := hA.trans_le (le_of_not_gt hl)
      have hqc :=
        (oscillatoryFactor_hasDerivAt x m v a c h hm hv hcPos hsafe_l).continuousAt
      convert!
        ((Complex.continuous_ofReal.comp
          (continuous_trapezoid L₁ L₂)).continuousAt.mul hqc) using 1 <;>
        simp [f, q]

  have hFT : ∀ n : ℤ, 𝓕 f n =
      pieceFourier h01 F₀ n + pieceFourier h12 F₁ n + pieceFourier h23 F₂ n := by
    intro n
    rw [pieceFourier_eq_integral h01, pieceFourier_eq_integral h12,
      pieceFourier_eq_integral h23, Real.fourier_real_eq_integral_exp_smul]
    simp_rw [real_fourier_kernel_eq_e, smul_eq_mul]
    let integrand : ℝ → ℂ := fun l => e (-((n : ℝ) * l)) * f l
    have hint : Continuous integrand :=
      (PS.continuous_e_comp (by fun_prop)).mul hf
    have hsupp : Function.support integrand ⊆
        Ioc (((L₁ - 1 : ℤ) : ℝ)) (((L₂ + 1 : ℤ) : ℝ)) := by
      intro l hl
      have htrap : trapezoid (L₁ : ℝ) (L₂ : ℝ) l ≠ 0 := by
        intro hz
        apply hl
        simp [integrand, f, hz]
      constructor
      · by_contra hle
        exact htrap (trapezoid_eq_zero_of_le (by
          simpa only [Int.cast_sub, Int.cast_one] using (le_of_not_gt hle)))
      · by_contra hge
        exact htrap (trapezoid_eq_zero_of_ge (by
          simpa only [Int.cast_add, Int.cast_one] using (le_of_not_ge hge)))
    have heq₀ :
        (∫ l in (((L₁ - 1 : ℤ) : ℝ))..(L₁ : ℝ), integrand l) =
          ∫ l in (((L₁ - 1 : ℤ) : ℝ))..(L₁ : ℝ),
            e (-((n : ℝ) * l)) * F₀ l := by
      apply integral_congr
      intro l hl
      have hl' : l ∈ Icc (((L₁ - 1 : ℤ) : ℝ)) (L₁ : ℝ) := by
        simpa [uIcc_of_le h01R.le] using hl
      have ht := trapezoid_eq_leftRamp h12R
        (by simpa only [Int.cast_sub, Int.cast_one] using hl'.1) hl'.2
      simp only [integrand, f]
      rw [ht]
      simp [F₀]
    have heq₁ :
        (∫ l in (L₁ : ℝ)..(L₂ : ℝ), integrand l) =
          ∫ l in (L₁ : ℝ)..(L₂ : ℝ), e (-((n : ℝ) * l)) * F₁ l := by
      apply integral_congr
      intro l hl
      have hl' : l ∈ Icc (L₁ : ℝ) (L₂ : ℝ) := by
        simpa [uIcc_of_le h12R.le] using hl
      simp only [integrand, f]
      rw [trapezoid_eq_one hl'.1 hl'.2]
      simp [F₁]
    have heq₂ :
        (∫ l in (L₂ : ℝ)..(((L₂ + 1 : ℤ) : ℝ)), integrand l) =
          ∫ l in (L₂ : ℝ)..(((L₂ + 1 : ℤ) : ℝ)),
            e (-((n : ℝ) * l)) * F₂ l := by
      apply integral_congr
      intro l hl
      have hl' : l ∈ Icc (L₂ : ℝ) (((L₂ + 1 : ℤ) : ℝ)) := by
        simpa [uIcc_of_le h23R.le] using hl
      have ht := trapezoid_eq_rightRamp h12R hl'.1
        (by simpa only [Int.cast_add, Int.cast_one] using hl'.2)
      simp only [integrand, f]
      rw [ht]
      simp [F₂]
    change (∫ l : ℝ, integrand l) = _
    calc
      (∫ l : ℝ, integrand l) =
          ∫ l in (((L₁ - 1 : ℤ) : ℝ))..(((L₂ + 1 : ℤ) : ℝ)), integrand l :=
        (integral_eq_integral_of_support_subset hsupp).symm
      _ = (∫ l in (((L₁ - 1 : ℤ) : ℝ))..(L₂ : ℝ), integrand l) +
          ∫ l in (L₂ : ℝ)..(((L₂ + 1 : ℤ) : ℝ)), integrand l :=
        (integral_add_adjacent_intervals (hint.intervalIntegrable _ _)
          (hint.intervalIntegrable _ _)).symm
      _ = ((∫ l in (((L₁ - 1 : ℤ) : ℝ))..(L₁ : ℝ), integrand l) +
          ∫ l in (L₁ : ℝ)..(L₂ : ℝ), integrand l) +
          ∫ l in (L₂ : ℝ)..(((L₂ + 1 : ℤ) : ℝ)), integrand l := by
        apply congrArg (fun z : ℂ =>
          z + ∫ l in (L₂ : ℝ)..(((L₂ + 1 : ℤ) : ℝ)), integrand l)
        exact (integral_add_adjacent_intervals (hint.intervalIntegrable _ _)
          (hint.intervalIntegrable _ _)).symm
      _ = _ := by rw [heq₀, heq₁, heq₂]

  have hsum : Summable fun n : ℤ => 𝓕 f n :=
    summable_of_three_piece_parts h01 h12 h23 hF₀ hF₁ hF₂ hd₀ hd₁ hd₂
      hi₀ hi₁ hi₂ hL2₀ hL2₁ hL2₂ hboundary hFT

  have hdecay : f =O[cocompact ℝ] fun l : ℝ => |l| ^ (-(2 : ℝ)) := by
    apply Filter.Eventually.isBigO
    filter_upwards [((isCompact_Icc : IsCompact
      (Icc (((L₁ - 1 : ℤ) : ℝ)) (((L₂ + 1 : ℤ) : ℝ)))).compl_mem_cocompact)] with l hl
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hl
    rcases hl with hl | hl
    · have hz : trapezoid (L₁ : ℝ) (L₂ : ℝ) l = 0 :=
        trapezoid_eq_zero_of_le (by
          simpa only [Int.cast_sub, Int.cast_one] using hl.le)
      rw [show f l = 0 by simp [f, hz], norm_zero]
      positivity
    · have hz : trapezoid (L₁ : ℝ) (L₂ : ℝ) l = 0 :=
        trapezoid_eq_zero_of_ge (by
          simpa only [Int.cast_add, Int.cast_one] using hl.le)
      rw [show f l = 0 by simp [f, hz], norm_zero]
      positivity

  have hpoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    hf one_lt_two hdecay hsum 0
  have hpoisson0 : (∑' n : ℤ, f n) = ∑' n : ℤ, 𝓕 f n := by
    simpa only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] using hpoisson

  have hfinite : (Function.support fun n : ℤ => f n).Finite := by
    apply (Set.finite_Icc (L₁ - 1) (L₂ + 1)).subset
    intro n hn
    have htrap : trapezoid (L₁ : ℝ) (L₂ : ℝ) n ≠ 0 := by
      intro hz
      apply hn
      simp [f, hz]
    constructor
    · by_contra hle
      apply htrap
      apply trapezoid_eq_zero_of_le
      exact_mod_cast le_of_not_ge hle
    · by_contra hge
      apply htrap
      apply trapezoid_eq_zero_of_ge
      exact_mod_cast le_of_not_ge hge

  have htransform : ∀ n : ℤ,
      𝓕 f n = trapezoidIntegral x h m v L₁ L₂ c
        (-((a : ℤ) * (h : ℤ)) - (c : ℤ) * n) := by
    intro n
    rw [Real.fourier_real_eq_integral_exp_smul]
    unfold trapezoidIntegral
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun l => by
      change Complex.exp ((-2 * π * l * (n : ℝ) : ℝ) * Complex.I) • f l = _
      rw [real_fourier_kernel_eq_e]
      simp only [smul_eq_mul, f, q]
      calc
        e (-((n : ℝ) * l)) *
            ((trapezoid (L₁ : ℝ) (L₂ : ℝ) l : ℂ) *
              oscillatoryFactor x m v a c h l) =
            (trapezoid (L₁ : ℝ) (L₂ : ℝ) l : ℂ) *
              (e (-((n : ℝ) * l)) * oscillatoryFactor x m v a c h l) := by ring
        _ = (trapezoid (L₁ : ℝ) (L₂ : ℝ) l : ℂ) *
            e (-((n : ℝ) * l) + shiftedPhase x m v a c h l) := by
              rw [oscillatoryFactor, ← KL.e_add]
        _ = (trapezoid (L₁ : ℝ) (L₂ : ℝ) l : ℂ) *
            e (rPhase x h m v l +
              ((-((a : ℤ) * (h : ℤ)) - (c : ℤ) * n : ℤ) : ℝ) * l / c) := by
              congr 2
              unfold shiftedPhase
              have hc0 : (c : ℝ) ≠ 0 := hcR.ne'
              push_cast
              field_simp
              ring

  calc
    (∑ᶠ l : ℤ, (trapezoid L₁ L₂ l : ℂ) *
        e (-((a : ℝ) * h * l / c) + rPhase x h m v l)) =
        ∑' l : ℤ, f l := by
          simpa [f, q, oscillatoryFactor, shiftedPhase] using
            (tsum_eq_finsum hfinite).symm
    _ = ∑' n : ℤ, 𝓕 f n := hpoisson0
    _ = ∑' n : ℤ, trapezoidIntegral x h m v L₁ L₂ c
        (-((a : ℤ) * (h : ℤ)) - (c : ℤ) * n) := tsum_congr htransform
    _ = ∑' k : ℤ,
        if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
          trapezoidIntegral x h m v L₁ L₂ c k else 0 :=
      tsum_residueClass (trapezoidIntegral x h m v L₁ L₂ c)
        (-((a : ℤ) * (h : ℤ))) (c : ℤ) hcZ

end LeanProofs.IntegerPoints
