import IntegerPoints.ExponentialSums
import IntegerPoints.SineIntegral
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Towards the truncated Perron formula (Zhai–Cao, Lemma 2)

Stage A: the basic integral identity.  For real `u, v` and `T > 0`,
`∫_{-T}^{T} (e^{itu} - e^{itv}) / t dt = 2 i (Si(Tu) - Si(Tv))`,
since the real part `(cos tu - cos tv)/t` is odd and the imaginary part
`(sin tu - sin tv)/t` is even with `∫₀^T sin(tu)/t dt = Si(Tu)`.
-/

open Real MeasureTheory intervalIntegral Filter Topology
open LeanProofs.IntegerPoints.SineIntegral

namespace LeanProofs.IntegerPoints

namespace Perron

/-- `‖e^{ix} - 1‖ ≤ |x|`. -/
theorem norm_exp_I_sub_one_le (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
  have hsq : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos x := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.one_im]
    linear_combination Real.cos_sq_add_sin_sq x
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  rw [← sq_le_sq₀ (norm_nonneg _) (abs_nonneg _), hsq, sq_abs]
  linarith

/-- The kernel `(e^{itu} - e^{itv}) / t`. -/
noncomputable def ker (u v t : ℝ) : ℂ :=
  (Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) - Complex.exp (((t * v : ℝ) : ℂ) * Complex.I)) / t

/-- `‖(e^{itu} - e^{itv}) / t‖ ≤ |u - v|`. -/
theorem norm_ker_le (u v t : ℝ) : ‖ker u v t‖ ≤ |u - v| := by
  unfold ker
  rcases eq_or_ne t 0 with h | h
  · simp [h]
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (abs_pos.2 h)]
    have hsplit : Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((t * v : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((t * v : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (((t * (u - v) : ℝ) : ℂ) * Complex.I) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    calc ‖Complex.exp (((t * (u - v) : ℝ) : ℂ) * Complex.I) - 1‖ ≤ |t * (u - v)| :=
          norm_exp_I_sub_one_le _
      _ = |u - v| * |t| := by rw [abs_mul, mul_comm]

/-- The real and imaginary parts of the kernel. -/
theorem ker_eq (u v t : ℝ) :
    ker u v t = ((Real.cos (t * u) - Real.cos (t * v)) / t : ℝ) +
      ((Real.sin (t * u) - Real.sin (t * v)) / t : ℝ) * Complex.I := by
  unfold ker
  rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  rcases eq_or_ne t 0 with h | h
  · simp [h]
  · field_simp
    ring

theorem measurable_cos_part (u v : ℝ) :
    Measurable fun t : ℝ => (Real.cos (t * u) - Real.cos (t * v)) / t := by fun_prop

theorem measurable_sin_part (u v : ℝ) :
    Measurable fun t : ℝ => (Real.sin (t * u) - Real.sin (t * v)) / t := by fun_prop

theorem abs_cos_part_le (u v t : ℝ) : |(Real.cos (t * u) - Real.cos (t * v)) / t| ≤ |u - v| := by
  have h := norm_ker_le u v t
  rw [ker_eq] at h
  set c := (Real.cos (t * u) - Real.cos (t * v)) / t with hc
  set s := (Real.sin (t * u) - Real.sin (t * v)) / t with hs
  have hre : ((c : ℂ) + (s : ℂ) * Complex.I).re = c := by simp
  calc |c| = |((c : ℂ) + (s : ℂ) * Complex.I).re| := by rw [hre]
    _ ≤ ‖(c : ℂ) + (s : ℂ) * Complex.I‖ := Complex.abs_re_le_norm _
    _ ≤ |u - v| := h

theorem abs_sin_part_le (u v t : ℝ) : |(Real.sin (t * u) - Real.sin (t * v)) / t| ≤ |u - v| := by
  have h := norm_ker_le u v t
  rw [ker_eq] at h
  set c := (Real.cos (t * u) - Real.cos (t * v)) / t with hc
  set s := (Real.sin (t * u) - Real.sin (t * v)) / t with hs
  have him : ((c : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
  calc |s| = |((c : ℂ) + (s : ℂ) * Complex.I).im| := by rw [him]
    _ ≤ ‖(c : ℂ) + (s : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
    _ ≤ |u - v| := h

/-- A bounded measurable real function is interval integrable, also as a complex function. -/
theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ t, |f t| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => C) intervalIntegrable_const
    hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      dsimp only
      rw [Real.norm_eq_abs]
      exact hb t)

theorem intervalIntegrable_ofReal_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ t, |f t| ≤ C) (a b : ℝ) : IntervalIntegrable (fun t => (f t : ℂ)) volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => C) intervalIntegrable_const
    (Complex.measurable_ofReal.comp hf).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      dsimp only
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hb t)

theorem intervalIntegrable_cos_part (u v a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (Real.cos (t * u) - Real.cos (t * v)) / t) volume a b :=
  intervalIntegrable_of_bounded (measurable_cos_part u v) (abs_cos_part_le u v) a b

theorem intervalIntegrable_sin_part (u v a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (Real.sin (t * u) - Real.sin (t * v)) / t) volume a b :=
  intervalIntegrable_of_bounded (measurable_sin_part u v) (abs_sin_part_le u v) a b

/-- `∫_{-T}^{T} f = 0` for odd interval-integrable `f`. -/
theorem integral_odd (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (hf : ∀ t, f (-t) = -f t)
    (hint : IntervalIntegrable f volume (-T) T) :
    ∫ t in (-T)..T, f t = 0 := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (-T) T := Set.mem_uIcc.2 (Or.inl ⟨by linarith, hT⟩)
  have hint1 : IntervalIntegrable f volume (-T) 0 :=
    hint.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc h0)
  have hint2 : IntervalIntegrable f volume 0 T :=
    hint.mono_set (Set.uIcc_subset_uIcc h0 Set.right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have : ∫ t in (-T)..0, f t = ∫ t in (0 : ℝ)..T, f (-t) := by
    rw [intervalIntegral.integral_comp_neg f, neg_zero]
  rw [this, intervalIntegral.integral_congr (fun t _ => hf t), intervalIntegral.integral_neg]
  ring

/-- `∫_{-T}^{T} f = 2 ∫₀^T f` for even interval-integrable `f`. -/
theorem integral_even (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (hf : ∀ t, f (-t) = f t)
    (hint : IntervalIntegrable f volume (-T) T) :
    ∫ t in (-T)..T, f t = 2 * ∫ t in (0 : ℝ)..T, f t := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (-T) T := Set.mem_uIcc.2 (Or.inl ⟨by linarith, hT⟩)
  have hint1 : IntervalIntegrable f volume (-T) 0 :=
    hint.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc h0)
  have hint2 : IntervalIntegrable f volume 0 T :=
    hint.mono_set (Set.uIcc_subset_uIcc h0 Set.right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have : ∫ t in (-T)..0, f t = ∫ t in (0 : ℝ)..T, f (-t) := by
    rw [intervalIntegral.integral_comp_neg f, neg_zero]
  rw [this, intervalIntegral.integral_congr (fun t _ => hf t)]
  ring

/-- `∫₀^T sin(t u)/t dt = Si(T u)`. -/
theorem integral_sin_div_eq_Si (u T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.sin (t * u) / t = Si (T * u) := by
  rcases eq_or_ne u 0 with h | h
  · simp [h, Si_zero]
  · rw [mul_comm T u]
    unfold Si
    have h1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := T) (f := SineIntegral.sinc) h
    rw [mul_zero] at h1
    have h2 : ∫ t in (0 : ℝ)..T, Real.sin (t * u) / t = ∫ t in (0 : ℝ)..T, u * SineIntegral.sinc (u * t) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [SineIntegral.sinc]
      rcases eq_or_ne t 0 with ht | ht
      · simp [ht]
      · field_simp
    rw [h2, intervalIntegral.integral_const_mul, h1, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ h, one_mul]

theorem abs_sin_div_le (u t : ℝ) : |Real.sin (t * u) / t| ≤ |u| := by
  rcases eq_or_ne t 0 with h | h
  · simp [h]
  · rw [abs_div, div_le_iff₀ (abs_pos.2 h)]
    calc |Real.sin (t * u)| ≤ |t * u| := Real.abs_sin_le_abs
      _ = |u| * |t| := by rw [abs_mul, mul_comm]

theorem intervalIntegrable_sin_div (u a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.sin (t * u) / t) volume a b :=
  intervalIntegrable_of_bounded (by fun_prop) (abs_sin_div_le u) a b

/-- The basic identity
`∫_{-T}^{T} (e^{itu} - e^{itv})/t dt = 2 i (Si(Tu) - Si(Tv))`. -/
theorem integral_ker (u v T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, ker u v t = 2 * Complex.I * ((Si (T * u) - Si (T * v) : ℝ) : ℂ) := by
  simp_rw [ker_eq]
  rw [intervalIntegral.integral_add
    (intervalIntegrable_ofReal_of_bounded (measurable_cos_part u v) (abs_cos_part_le u v) _ _)
    ((intervalIntegrable_ofReal_of_bounded (measurable_sin_part u v) (abs_sin_part_le u v) _ _).mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  rw [integral_odd _ T hT (fun t => by
      simp only [neg_mul, Real.cos_neg]
      rw [div_neg])
    (intervalIntegrable_cos_part u v _ _)]
  rw [integral_even _ T hT (fun t => by
      simp only [neg_mul, Real.sin_neg]
      rw [div_neg]
      ring)
    (intervalIntegrable_sin_part u v _ _)]
  have hsplit : ∫ t in (0 : ℝ)..T, (Real.sin (t * u) - Real.sin (t * v)) / t =
      Si (T * u) - Si (T * v) := by
    rw [intervalIntegral.integral_congr
        (fun t _ => sub_div (Real.sin (t * u)) (Real.sin (t * v)) t),
      intervalIntegral.integral_sub (intervalIntegrable_sin_div u _ _)
        (intervalIntegrable_sin_div v _ _),
      integral_sin_div_eq_Si, integral_sin_div_eq_Si]
  rw [hsplit]
  push_cast
  ring

/-! ### Stage B: the integral in Lemma 2 -/

theorem measurable_ker (u v : ℝ) : Measurable (ker u v) := by
  unfold ker
  fun_prop

theorem intervalIntegrable_ker (u v a b : ℝ) : IntervalIntegrable (ker u v) volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => |u - v|) intervalIntegrable_const
    (measurable_ker u v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      dsimp only
      exact norm_ker_le u v t)

/-- `x^{it} = e^{i t log x}` for real `x > 0`. -/
theorem cpow_I_mul (x t : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ (Complex.I * t) = Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  congr 1
  push_cast
  ring

/-- The summand of the Perron integrand in terms of the kernel. -/
theorem term_eq (a : ℂ) (l M N t : ℝ) (hl : 0 < l) (hM : 0 < M) (hN : 0 < N) :
    a / (l : ℂ) ^ (Complex.I * t) * (((N : ℂ) ^ (Complex.I * t) - (M : ℂ) ^ (Complex.I * t)) / t) =
      a * ker (Real.log N - Real.log l) (Real.log M - Real.log l) t := by
  rw [cpow_I_mul l t hl, cpow_I_mul M t hM, cpow_I_mul N t hN]
  unfold ker
  have e1 : (((t * (Real.log N - Real.log l) : ℝ) : ℂ) * Complex.I) =
      ((t * Real.log N : ℝ) : ℂ) * Complex.I - ((t * Real.log l : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have e2 : (((t * (Real.log M - Real.log l) : ℝ) : ℂ) * Complex.I) =
      ((t * Real.log M : ℝ) : ℂ) * Complex.I - ((t * Real.log l : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e1, e2, Complex.exp_sub, Complex.exp_sub]
  have hne := Complex.exp_ne_zero (((t * Real.log l : ℝ) : ℂ) * Complex.I)
  field_simp

/-- The weight `(Si(Tu) - Si(Tv)) / π`. -/
noncomputable def w (T u v : ℝ) : ℝ := (Si (T * u) - Si (T * v)) / π

/-- **The Perron integral**: for `0 < M, N`, `L ≥ 1`,
`(2πi)⁻¹ ∫_{-T}^{T} (∑_l a_l l^{-it}) (N^{it} - M^{it})/t dt
   = ∑_l a_l (Si(T log(N/l)) - Si(T log(M/l))) / π`. -/
theorem perron_integral (L c M N T : ℝ) (a : ℕ → ℂ) (hL : 1 ≤ L) (hM : 0 < M) (hN : 0 < N)
    (hT : 0 ≤ T) :
    (1 / (2 * Real.pi * Complex.I)) *
        ∫ t in (-T)..T,
          (∑ l ∈ intRange L (c * L), a l / (l : ℂ) ^ (Complex.I * t)) *
            (((N : ℂ) ^ (Complex.I * t) - (M : ℂ) ^ (Complex.I * t)) / t) =
      ∑ l ∈ intRange L (c * L),
        a l * ((w T (Real.log N - Real.log l) (Real.log M - Real.log l) : ℝ) : ℂ) := by
  have hpos : ∀ l ∈ intRange L (c * L), (0 : ℝ) < l := by
    intro l hl
    simp only [intRange, Finset.mem_Ioc] at hl
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hl.1
  have hF : ∀ t : ℝ,
      (∑ l ∈ intRange L (c * L), a l / (l : ℂ) ^ (Complex.I * t)) *
          (((N : ℂ) ^ (Complex.I * t) - (M : ℂ) ^ (Complex.I * t)) / t) =
        ∑ l ∈ intRange L (c * L), a l * ker (Real.log N - Real.log l) (Real.log M - Real.log l) t := by
    intro t
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l hl => term_eq (a l) l M N t (hpos l hl) hM hN
  simp_rw [hF]
  rw [intervalIntegral.integral_finsetSum
    (fun l _ => (intervalIntegrable_ker _ _ _ _).const_mul (a l)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_ker _ _ T hT, w]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI := Complex.I_ne_zero
  push_cast
  field_simp


/-! ### Stage C1–C3: bounds on the weights -/

/-- `|Si x / π - 1/2| ≤ 2 / (π x)` for `x > 0`. -/
theorem abs_s_sub_half (x : ℝ) (hx : 0 < x) : |Si x / π - 1 / 2| ≤ 2 / (π * x) := by
  have h := abs_Si_sub_pi_div_two_le x hx
  have : Si x / π - 1 / 2 = (Si x - π / 2) / π := by field_simp
  rw [this, abs_div, abs_of_pos Real.pi_pos, div_le_div_iff₀ Real.pi_pos (by positivity)]
  calc |Si x - π / 2| * (π * x) ≤ 2 / x * (π * x) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 2 * π := by field_simp

/-- `|Si x / π + 1/2| ≤ 2 / (π |x|)` for `x < 0`. -/
theorem abs_s_add_half (x : ℝ) (hx : x < 0) : |Si x / π + 1 / 2| ≤ 2 / (π * |x|) := by
  have h := abs_s_sub_half (-x) (by linarith)
  rw [Si_neg] at h
  rw [abs_of_neg hx]
  have : -Si x / π - 1 / 2 = -(Si x / π + 1 / 2) := by ring
  rw [this, abs_neg] at h
  exact h

/-- `|Si x / π| ≤ 3/2`. -/
theorem abs_s_le (x : ℝ) : |Si x / π| ≤ 3 / 2 := by
  have h3 : |Si x| ≤ 3 := by
    rcases le_or_gt 0 x with h | h
    · exact abs_Si_le_three x h
    · have := abs_Si_le_three (-x) (by linarith)
      rwa [Si_neg, abs_neg] at this
  rw [abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
  linarith [Real.two_le_pi]

/-- The indicator `χ(u, v) = [v < 0 < u]`. -/
noncomputable def chi (u v : ℝ) : ℝ := if v < 0 ∧ 0 < u then 1 else 0

theorem w_eq (T u v : ℝ) : w T u v = Si (T * u) / π - Si (T * v) / π := by
  unfold w
  ring

/-- The crude bound `|χ - w| ≤ 4`. -/
theorem chi_sub_w_crude (T u v : ℝ) : |chi u v - w T u v| ≤ 4 := by
  have h1 := abs_le.1 (abs_s_le (T * u))
  have h2 := abs_le.1 (abs_s_le (T * v))
  rw [w_eq, chi]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The sharp bound `|χ - w| ≤ (2/(πT)) (1/|u| + 1/|v|)` for `u, v ≠ 0`, `v < u`. -/
theorem chi_sub_w_le (T u v : ℝ) (hT : 0 < T) (hvu : v < u) (hu : u ≠ 0) (hv : v ≠ 0) :
    |chi u v - w T u v| ≤ 2 / (π * T) * (1 / |u| + 1 / |v|) := by
  rw [w_eq, chi]
  have eu : 2 / (π * (T * |u|)) = 2 / (π * T) * (1 / |u|) := by
    have : |u| ≠ 0 := abs_ne_zero.2 hu
    field_simp
  have ev : 2 / (π * (T * |v|)) = 2 / (π * T) * (1 / |v|) := by
    have : |v| ≠ 0 := abs_ne_zero.2 hv
    field_simp
  rcases lt_or_gt_of_ne hu with hu' | hu' <;> rcases lt_or_gt_of_ne hv with hv' | hv'
  · -- `v < u < 0`
    have Bu := abs_s_add_half (T * u) (by nlinarith)
    have Bv := abs_s_add_half (T * v) (by nlinarith)
    rw [abs_mul, abs_of_pos hT, eu] at Bu
    rw [abs_mul, abs_of_pos hT, ev] at Bv
    rw [if_neg (by intro h; linarith [h.2])]
    rw [abs_le] at Bu Bv ⊢
    constructor <;> linarith [Bu.1, Bu.2, Bv.1, Bv.2]
  · exact absurd hvu (by linarith)
  · -- `v < 0 < u`
    have Bu := abs_s_sub_half (T * u) (by positivity)
    have Bv := abs_s_add_half (T * v) (by nlinarith)
    have eu' : 2 / (π * (T * u)) = 2 / (π * T) * (1 / |u|) := by
      rw [abs_of_pos hu']
      field_simp
    rw [eu'] at Bu
    rw [abs_mul, abs_of_pos hT, ev] at Bv
    rw [if_pos ⟨hv', hu'⟩]
    rw [abs_le] at Bu Bv ⊢
    constructor <;> linarith [Bu.1, Bu.2, Bv.1, Bv.2]
  · -- `0 < v < u`
    have Bu := abs_s_sub_half (T * u) (by positivity)
    have Bv := abs_s_sub_half (T * v) (by positivity)
    have eu' : 2 / (π * (T * u)) = 2 / (π * T) * (1 / |u|) := by
      rw [abs_of_pos hu']
      field_simp
    have ev' : 2 / (π * (T * v)) = 2 / (π * T) * (1 / |v|) := by
      rw [abs_of_pos hv']
      field_simp
    rw [eu'] at Bu
    rw [ev'] at Bv
    rw [if_neg (by intro h; linarith [h.1])]
    rw [abs_le] at Bu Bv ⊢
    constructor <;> linarith [Bu.1, Bu.2, Bv.1, Bv.2]

/-- `|log x - log y| ≥ |x - y| / Y` for `0 < x, y ≤ Y`. -/
theorem abs_log_sub_ge (x y Y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxY : x ≤ Y) (hyY : y ≤ Y) :
    |x - y| / Y ≤ |Real.log x - Real.log y| := by
  wlog h : y ≤ x generalizing x y
  · have := this y x hy hx hyY hxY (by linarith)
    rwa [abs_sub_comm, abs_sub_comm (Real.log y)] at this
  · have hY : 0 < Y := lt_of_lt_of_le hx hxY
    rw [abs_of_nonneg (by linarith),
      abs_of_nonneg (by rw [sub_nonneg]; exact Real.log_le_log hy h)]
    have h1 : Real.log y - Real.log x ≤ y / x - 1 := by
      rw [← Real.log_div hy.ne' hx.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have h2 : (x - y) / Y ≤ (x - y) / x := div_le_div_of_nonneg_left (by linarith) hx hxY
    have h3 : (x - y) / x = 1 - y / x := by field_simp
    linarith


/-! ### Stage C4–C5: the sums over `l` -/

/-- `min 4 (a + b) ≤ min 4 a + min 4 b` for `a, b ≥ 0`. -/
theorem min_four_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : min 4 (a + b) ≤ min 4 a + min 4 b := by
  rcases le_or_gt 4 a with h1 | h1
  · rw [min_eq_left h1]
    have : min 4 (a + b) ≤ 4 := min_le_left _ _
    have : 0 ≤ min 4 b := le_min (by norm_num) hb
    linarith
  rcases le_or_gt 4 b with h2 | h2
  · rw [min_eq_left h2]
    have : min 4 (a + b) ≤ 4 := min_le_left _ _
    have : 0 ≤ min 4 a := le_min (by norm_num) ha
    linarith
  · rw [min_eq_right h1.le, min_eq_right h2.le]
    exact min_le_right _ _

/-- `min 4 (a y) ≤ max 4 a · min 1 y` for `a, y ≥ 0`. -/
theorem min_four_mul (a y : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y) : min 4 (a * y) ≤ max 4 a * min 1 y := by
  rcases le_or_gt 1 y with h | h
  · rw [min_eq_left h, mul_one]
    exact le_trans (min_le_left _ _) (le_max_left _ _)
  · rw [min_eq_right h.le]
    calc min 4 (a * y) ≤ a * y := min_le_right _ _
      _ ≤ max 4 a * y := mul_le_mul_of_nonneg_right (le_max_right _ _) hy

/-- The shell sum: for `l, l₀ ≤ K`, `∑_{l ∈ S, l ≠ l₀} 1/|l - l₀| ≤ 2 (1 + log K)`. -/
theorem shell_sum (S : Finset ℕ) (l₀ K : ℕ) (hK : 1 ≤ K) (hS : ∀ l ∈ S, l ≤ K) (hl₀ : l₀ ≤ K) :
    ∑ l ∈ S.filter (fun l => l ≠ l₀), 1 / |(l : ℝ) - l₀| ≤ 2 * (1 + Real.log K) := by
  classical
  set S' := S.filter (fun l => l ≠ l₀) with hS'
  set d : ℕ → ℕ := fun l => Int.natAbs ((l : ℤ) - l₀) with hd
  have hmaps : ∀ l ∈ S', d l ∈ Finset.Icc 1 K := by
    intro l hl
    rw [hS', Finset.mem_filter] at hl
    have := hS l hl.1
    rw [Finset.mem_Icc, hd]
    simp only
    constructor
    · rw [Nat.one_le_iff_ne_zero, ne_eq, Int.natAbs_eq_zero, sub_eq_zero]
      exact_mod_cast hl.2
    · omega
  have hval : ∀ l ∈ S', 1 / |(l : ℝ) - l₀| = 1 / (d l : ℝ) := by
    intro l _
    rw [hd]
    simp only
    congr 1
    rw [Nat.cast_natAbs]
    push_cast
    rfl
  have hfiber : ∀ k, ((S'.filter (fun l => d l = k)).card : ℝ) ≤ 2 := by
    intro k
    have hsub : S'.filter (fun l => d l = k) ⊆ {l₀ + k, l₀ - k} := by
      intro l hl
      rw [Finset.mem_filter, hd] at hl
      simp only at hl
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases Int.natAbs_eq ((l : ℤ) - l₀) with h | h <;> rw [hl.2] at h <;> omega
    have := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le l₀ (({l₀ - k} : Finset ℕ))
    rw [Finset.card_singleton] at h2
    calc ((S'.filter (fun l => d l = k)).card : ℝ) ≤ (({l₀ + k, l₀ - k} : Finset ℕ).card : ℝ) := by
          exact_mod_cast this
      _ ≤ 2 := by
          have : ({l₀ + k, l₀ - k} : Finset ℕ).card ≤ 2 := Finset.card_le_two
          exact_mod_cast this
  rw [Finset.sum_congr rfl hval, ← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ S'.filter (fun l => d l = k), 1 / (d l : ℝ)
      = ∑ k ∈ Finset.Icc 1 K, ((S'.filter (fun l => d l = k)).card : ℝ) * (1 / (k : ℝ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl (fun l hl => by
          rw [(Finset.mem_filter.1 hl).2] : ∀ l ∈ S'.filter (fun l => d l = k),
            1 / (d l : ℝ) = 1 / (k : ℝ)), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.Icc 1 K, 2 * (1 / (k : ℝ)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hfiber k) (by positivity)
    _ = 2 * (harmonic K : ℝ) := by
        rw [← Finset.mul_sum, harmonic, Rat.cast_sum]
        congr 1
        rw [show Finset.Icc 1 K = Finset.Ico 1 (K + 1) by
          ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
          Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        rw [add_comm, one_div]
    _ ≤ 2 * (1 + Real.log K) := by
        have := harmonic_le_one_add_log K
        linarith

/-- The per-endpoint weight `m_X(l)`. -/
noncomputable def mX (T X : ℝ) (l : ℕ) : ℝ :=
  if (l : ℝ) = X then 4 else min 4 (2 / (π * T) * (1 / |Real.log X - Real.log l|))

/-- The per-endpoint sum: for `L ≤ X ≤ cL`,
`∑_{l ∈ S} m_X(l) ≤ max 4 (2c/π) · perronEdge L T X + (8cL/(πT)) (1 + log(cL + 1))`. -/
theorem endpoint_sum (L c X T : ℝ) (hL : 1 ≤ L) (hc : 1 < c) (hX1 : L ≤ X) (hX2 : X ≤ c * L)
    (hT : 0 < T) :
    ∑ l ∈ intRange L (c * L), mX T X l ≤
      max 4 (2 * c / π) * perronEdge L T X + 8 * c * L / (π * T) * (1 + Real.log (c * L + 1)) := by
  classical
  have hc0 : 0 < c := by linarith
  set S := intRange L (c * L) with hS
  set l₀ : ℕ := ⌊X + 1 / 2⌋₊ with hl₀
  have hX0 : 0 < X := by linarith
  have hcL : 0 < c * L := by positivity
  have hl₀X : ((round X : ℤ) : ℝ) = (l₀ : ℝ) := by
    rw [round_eq, hl₀, ← Int.natCast_floor_eq_floor (by positivity)]
    push_cast
    rfl
  have hd : nearestIntDist X = |X - l₀| := by
    unfold nearestIntDist
    rw [hl₀X]
  have hhalf : |X - l₀| ≤ 1 / 2 := by
    rw [← hd]
    exact abs_sub_round X
  have hmemS : ∀ l ∈ S, (0 : ℝ) < l ∧ (l : ℝ) ≤ c * L := by
    intro l hl
    simp only [hS, intRange, Finset.mem_Ioc] at hl
    constructor
    · exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hl.1
    · exact_mod_cast (Nat.le_floor_iff hcL.le).1 hl.2
  have hpE0 : 0 ≤ perronEdge L T X := by
    unfold perronEdge
    split_ifs
    · norm_num
    · exact le_min (by norm_num)
        (div_nonneg (by linarith) (mul_nonneg hT.le (by unfold nearestIntDist; exact abs_nonneg _)))
  -- split off `l₀`
  have hsplit : ∑ l ∈ S, mX T X l =
      (if l₀ ∈ S then mX T X l₀ else 0) + ∑ l ∈ S.filter (fun l => l ≠ l₀), mX T X l := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l => l = l₀)]
    congr 1
    rw [Finset.filter_eq']
    split_ifs with h
    · rw [Finset.sum_singleton]
    · rw [Finset.sum_empty]
  -- the `l₀` term
  have hfirst : (if l₀ ∈ S then mX T X l₀ else 0) ≤ max 4 (2 * c / π) * perronEdge L T X := by
    split_ifs with hmem
    · unfold mX
      split_ifs with hXl
      · have h0 : nearestIntDist X = 0 := by rw [hd, hXl, sub_self, abs_zero]
        rw [perronEdge, if_pos h0, mul_one]
        exact le_max_left _ _
      · have hdpos : 0 < |X - l₀| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hXl))
        have hne : nearestIntDist X ≠ 0 := by rw [hd]; exact hdpos.ne'
        rw [perronEdge, if_neg hne, hd]
        obtain ⟨hl₀pos, hl₀le⟩ := hmemS l₀ hmem
        have hlog := abs_log_sub_ge X l₀ (c * L) hX0 hl₀pos hX2 hl₀le
        have hlogpos : 0 < |Real.log X - Real.log l₀| :=
          lt_of_lt_of_le (by positivity) hlog
        have h1 : 1 / |Real.log X - Real.log l₀| ≤ c * L / |X - l₀| := by
          rw [div_le_div_iff₀ hlogpos hdpos, one_mul]
          rw [div_le_iff₀ hcL] at hlog
          linarith
        have h2 : 2 / (π * T) * (1 / |Real.log X - Real.log l₀|) ≤
            2 * c / π * (L / (T * |X - l₀|)) := by
          calc 2 / (π * T) * (1 / |Real.log X - Real.log l₀|)
              ≤ 2 / (π * T) * (c * L / |X - l₀|) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 2 * c / π * (L / (T * |X - l₀|)) := by
                field_simp
        calc min 4 (2 / (π * T) * (1 / |Real.log X - Real.log l₀|))
            ≤ min 4 (2 * c / π * (L / (T * |X - l₀|))) := min_le_min_left _ h2
          _ ≤ max 4 (2 * c / π) * min 1 (L / (T * |X - l₀|)) :=
              min_four_mul _ _ (by positivity) (by positivity)
    · exact mul_nonneg (le_trans (by norm_num) (le_max_left _ _)) hpE0
  -- the remaining terms
  have hrest : ∑ l ∈ S.filter (fun l => l ≠ l₀), mX T X l ≤
      8 * c * L / (π * T) * (1 + Real.log (c * L + 1)) := by
    set K : ℕ := ⌊c * L⌋₊ + 1 with hK
    have hK1 : 1 ≤ K := by omega
    have hSK : ∀ l ∈ S, l ≤ K := by
      intro l hl
      simp only [hS, intRange, Finset.mem_Ioc] at hl
      omega
    have hl₀K : l₀ ≤ K := by
      rw [hl₀, hK, ← Nat.floor_add_one hcL.le]
      exact Nat.floor_le_floor (by linarith)
    have hshell := shell_sum S l₀ K hK1 hSK hl₀K
    have hKle : Real.log (K : ℝ) ≤ Real.log (c * L + 1) := by
      refine Real.log_le_log (by positivity) ?_
      rw [hK]
      push_cast
      linarith [Nat.floor_le hcL.le]
    calc ∑ l ∈ S.filter (fun l => l ≠ l₀), mX T X l
        ≤ ∑ l ∈ S.filter (fun l => l ≠ l₀), 4 * c * L / (π * T) * (1 / |(l : ℝ) - l₀|) := by
          refine Finset.sum_le_sum fun l hl => ?_
          rw [Finset.mem_filter] at hl
          obtain ⟨hlpos, hlle⟩ := hmemS l hl.1
          have hlX : (l : ℝ) ≠ X := by
            intro h
            apply hl.2
            rw [hl₀, ← h, eq_comm, Nat.floor_eq_iff (by positivity)]
            push_cast
            constructor <;> linarith
          unfold mX
          rw [if_neg hlX]
          have hlog := abs_log_sub_ge X l (c * L) hX0 hlpos hX2 hlle
          have hXl : 0 < |X - l| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hlX))
          have hlogpos : 0 < |Real.log X - Real.log l| := lt_of_lt_of_le (by positivity) hlog
          have h1 : (1 : ℝ) ≤ |(l : ℝ) - l₀| := by
            have hne : (l : ℤ) ≠ l₀ := by exact_mod_cast hl.2
            have : (1 : ℤ) ≤ |(l : ℤ) - l₀| := Int.one_le_abs (sub_ne_zero.2 hne)
            have h' : ((1 : ℤ) : ℝ) ≤ ((|(l : ℤ) - l₀| : ℤ) : ℝ) := by exact_mod_cast this
            push_cast at h'
            exact h'
          have h2 : |(l : ℝ) - l₀| ≤ |X - l| + |X - l₀| := by
            calc |(l : ℝ) - l₀| = |(l - X) + (X - l₀)| := by congr 1; ring
              _ ≤ |(l : ℝ) - X| + |X - l₀| := abs_add_le _ _
              _ = |X - l| + |X - l₀| := by rw [abs_sub_comm (l : ℝ) X]
          have hdist : |(l : ℝ) - l₀| / 2 ≤ |X - l| := by linarith
          have h3 : 1 / |Real.log X - Real.log l| ≤ c * L / |X - l| := by
            rw [div_le_div_iff₀ hlogpos hXl, one_mul]
            rw [div_le_iff₀ hcL] at hlog
            linarith
          have h4 : c * L / |X - l| ≤ c * L * (2 / |(l : ℝ) - l₀|) := by
            rw [div_eq_mul_one_div]
            apply mul_le_mul_of_nonneg_left _ hcL.le
            rw [div_le_div_iff₀ hXl (by linarith)]
            linarith
          calc min 4 (2 / (π * T) * (1 / |Real.log X - Real.log l|))
              ≤ 2 / (π * T) * (1 / |Real.log X - Real.log l|) := min_le_right _ _
            _ ≤ 2 / (π * T) * (c * L * (2 / |(l : ℝ) - l₀|)) :=
                mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
            _ = 4 * c * L / (π * T) * (1 / |(l : ℝ) - l₀|) := by
                field_simp
                norm_num
      _ = 4 * c * L / (π * T) * ∑ l ∈ S.filter (fun l => l ≠ l₀), 1 / |(l : ℝ) - l₀| := by
          rw [Finset.mul_sum]
      _ ≤ 4 * c * L / (π * T) * (2 * (1 + Real.log K)) :=
          mul_le_mul_of_nonneg_left hshell (by positivity)
      _ ≤ 8 * c * L / (π * T) * (1 + Real.log (c * L + 1)) := by
          have h0 : 0 ≤ 8 * c * L / (π * T) := by positivity
          calc 4 * c * L / (π * T) * (2 * (1 + Real.log K))
              = 8 * c * L / (π * T) * (1 + Real.log K) := by ring
            _ ≤ 8 * c * L / (π * T) * (1 + Real.log (c * L + 1)) :=
                mul_le_mul_of_nonneg_left (by linarith) h0
  rw [hsplit]
  linarith


/-! ### Stage C6: assembly -/

theorem abs_w_le (T u v : ℝ) : |w T u v| ≤ 3 := by
  rw [w_eq]
  have h1 := abs_le.1 (abs_s_le (T * u))
  have h2 := abs_le.1 (abs_s_le (T * v))
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem mX_nonneg (T X : ℝ) (hT : 0 < T) (l : ℕ) : 0 ≤ mX T X l := by
  unfold mX
  split_ifs
  · norm_num
  · exact le_min (by norm_num) (by positivity)

theorem perronEdge_nonneg (L T X : ℝ) (hL : 0 ≤ L) (hT : 0 < T) : 0 ≤ perronEdge L T X := by
  unfold perronEdge
  split_ifs
  · norm_num
  · exact le_min (by norm_num)
      (div_nonneg hL (mul_nonneg hT.le (by unfold nearestIntDist; exact abs_nonneg _)))

/-- The per-`l` bound `|χ_l - w_l| ≤ m_N(l) + m_M(l)`. -/
theorem E_le (L c M N T : ℝ) (hL : 1 ≤ L) (hLM : L ≤ M) (hMN : M < N) (hT : 0 < T)
    (l : ℕ) (hl : l ∈ intRange L (c * L)) :
    |(if l ∈ intRange M N then (1 : ℝ) else 0) -
        w T (Real.log N - Real.log l) (Real.log M - Real.log l)| ≤ mX T N l + mX T M l := by
  classical
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hl0 : (0 : ℝ) < l := by
    simp only [intRange, Finset.mem_Ioc] at hl
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hl.1
  set u := Real.log N - Real.log l with hu
  set v := Real.log M - Real.log l with hv
  have hvu : v < u := by
    rw [hu, hv]
    have := Real.log_lt_log hM0 hMN
    linarith
  have hχ1 : |(if l ∈ intRange M N then (1 : ℝ) else 0)| ≤ 1 := by
    split_ifs <;> simp
  have hcrude : |(if l ∈ intRange M N then (1 : ℝ) else 0) - w T u v| ≤ 4 := by
    calc |(if l ∈ intRange M N then (1 : ℝ) else 0) - w T u v|
        ≤ |(if l ∈ intRange M N then (1 : ℝ) else 0)| + |w T u v| := abs_sub _ _
      _ ≤ 1 + 3 := add_le_add hχ1 (abs_w_le T u v)
      _ = 4 := by norm_num
  by_cases hlN : (l : ℝ) = N
  · have h4 : mX T N l = 4 := by unfold mX; rw [if_pos hlN]
    rw [h4]
    linarith [mX_nonneg T M hT l]
  by_cases hlM : (l : ℝ) = M
  · have h4 : mX T M l = 4 := by unfold mX; rw [if_pos hlM]
    rw [h4]
    linarith [mX_nonneg T N hT l]
  -- both `u` and `v` are nonzero
  have hu0 : u ≠ 0 := by
    rw [hu, sub_ne_zero]
    intro h
    exact hlN ((Real.log_injOn_pos (Set.mem_Ioi.2 hl0) (Set.mem_Ioi.2 hN0) h.symm))
  have hv0 : v ≠ 0 := by
    rw [hv, sub_ne_zero]
    intro h
    exact hlM ((Real.log_injOn_pos (Set.mem_Ioi.2 hl0) (Set.mem_Ioi.2 hM0) h.symm))
  have hχ : (if l ∈ intRange M N then (1 : ℝ) else 0) = chi u v := by
    have hiff : l ∈ intRange M N ↔ (v < 0 ∧ 0 < u) := by
      simp only [intRange, Finset.mem_Ioc, Nat.floor_lt hM0.le, Nat.le_floor_iff hN0.le]
      rw [hu, hv, sub_neg, sub_pos, Real.log_lt_log_iff hM0 hl0, Real.log_lt_log_iff hl0 hN0]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, lt_of_le_of_ne h2 hlN⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2.le⟩
    unfold chi
    by_cases h : l ∈ intRange M N
    · rw [if_pos h, if_pos (hiff.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]
  rw [hχ] at hcrude ⊢
  have hsharp := chi_sub_w_le T u v hT hvu hu0 hv0
  have hmN : mX T N l = min 4 (2 / (π * T) * (1 / |u|)) := by
    unfold mX
    rw [if_neg hlN]
  have hmM : mX T M l = min 4 (2 / (π * T) * (1 / |v|)) := by
    unfold mX
    rw [if_neg hlM]
  rw [hmN, hmM]
  have ha : 0 ≤ 2 / (π * T) * (1 / |u|) := by positivity
  have hb : 0 ≤ 2 / (π * T) * (1 / |v|) := by positivity
  calc |chi u v - w T u v| ≤ min 4 (2 / (π * T) * (1 / |u|) + 2 / (π * T) * (1 / |v|)) :=
        le_min hcrude (by rw [← mul_add]; exact hsharp)
    _ ≤ _ := min_four_add _ _ ha hb

/-- `1 + log(cL + 1) ≤ K₂ log(1 + L)` with `K₂ = (1 + log(c+1))/log 2 + 1`. -/
theorem log_bookkeeping (c L : ℝ) (hc : 1 < c) (hL : 1 ≤ L) :
    1 + Real.log (c * L + 1) ≤ ((1 + Real.log (c + 1)) / Real.log 2 + 1) * Real.log (1 + L) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ Real.log (1 + L) := Real.log_le_log (by norm_num) (by linarith)
  have hc1 : 0 ≤ Real.log (c + 1) := Real.log_nonneg (by linarith)
  have h1 : Real.log (c * L + 1) ≤ Real.log (c + 1) + Real.log (1 + L) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    refine Real.log_le_log (by positivity) ?_
    nlinarith
  have h2 : 1 + Real.log (c + 1) ≤ (1 + Real.log (c + 1)) / Real.log 2 * Real.log (1 + L) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  nlinarith

end Perron

open Perron in
/-- **Zhai–Cao, Lemma 2** (`zhaiCao_lemma2`), the truncated Perron formula. -/
theorem zhaiCao_lemma2_holds : zhaiCao_lemma2 := by
  intro c A hc hA
  classical
  set K₁ : ℝ := max 4 (2 * c / π) with hK₁
  set K₂ : ℝ := (1 + Real.log (c + 1)) / Real.log 2 + 1 with hK₂
  have hc0 : 0 < c := by linarith
  have hK₁0 : 0 ≤ K₁ := le_trans (by norm_num) (le_max_left _ _)
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂]
    have : 0 ≤ Real.log (c + 1) := Real.log_nonneg (by linarith)
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨A * max K₁ (16 * c / π * K₂), fun L M N T a ha hL hLM hMN hNc hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  set S := intRange L (c * L) with hS
  rw [perron_integral L c M N T a hL hM0 hN0 hT0.le]
  have hsub : intRange M N ⊆ S := by
    simp only [intRange, hS]
    exact Finset.Ioc_subset_Ioc (Nat.floor_le_floor hLM) (Nat.floor_le_floor hNc)
  have hleft : ∑ n ∈ intRange M N, a n = ∑ l ∈ S, (if l ∈ intRange M N then a l else 0) := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub]
  rw [hleft, ← Finset.sum_sub_distrib]
  have hterm : ∀ l ∈ S, (if l ∈ intRange M N then a l else 0) -
      a l * ((w T (Real.log N - Real.log l) (Real.log M - Real.log l) : ℝ) : ℂ) =
      a l * (((if l ∈ intRange M N then (1 : ℝ) else 0) -
        w T (Real.log N - Real.log l) (Real.log M - Real.log l) : ℝ) : ℂ) := by
    intro l _
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hterm]
  -- the sum of the errors
  have hE := fun l hl => E_le L c M N T hL hLM hMN hT0 l hl
  have hsumN := endpoint_sum L c N T hL hc (by linarith) hNc hT0
  have hsumM := endpoint_sum L c M T hL hc hLM (by linarith) hT0
  have hlogbk := log_bookkeeping c L hc hL
  have hpEM := perronEdge_nonneg L T M (by linarith) hT0
  have hpEN := perronEdge_nonneg L T N (by linarith) hT0
  have hLlog : 0 ≤ L * Real.log (1 + L) / T := by
    have : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
    positivity
  calc ‖∑ l ∈ S, a l * (((if l ∈ intRange M N then (1 : ℝ) else 0) -
          w T (Real.log N - Real.log l) (Real.log M - Real.log l) : ℝ) : ℂ)‖
      ≤ ∑ l ∈ S, ‖a l * (((if l ∈ intRange M N then (1 : ℝ) else 0) -
          w T (Real.log N - Real.log l) (Real.log M - Real.log l) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ S, A * (mX T N l + mX T M l) := by
        refine Finset.sum_le_sum fun l hl => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (ha l) (hE l hl) (abs_nonneg _) hA.le
    _ = A * (∑ l ∈ S, mX T N l + ∑ l ∈ S, mX T M l) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ A * ((K₁ * perronEdge L T N + 8 * c * L / (π * T) * (1 + Real.log (c * L + 1))) +
          (K₁ * perronEdge L T M + 8 * c * L / (π * T) * (1 + Real.log (c * L + 1)))) :=
        mul_le_mul_of_nonneg_left (add_le_add hsumN hsumM) hA.le
    _ = A * (K₁ * (perronEdge L T M + perronEdge L T N) +
          16 * c / π * (L / T) * (1 + Real.log (c * L + 1))) := by ring
    _ ≤ A * (K₁ * (perronEdge L T M + perronEdge L T N) +
          16 * c / π * (L / T) * (K₂ * Real.log (1 + L))) := by
        gcongr
    _ = A * (K₁ * (perronEdge L T M + perronEdge L T N) +
          (16 * c / π * K₂) * (L * Real.log (1 + L) / T)) := by ring
    _ ≤ A * (max K₁ (16 * c / π * K₂) * (perronEdge L T M + perronEdge L T N) +
          max K₁ (16 * c / π * K₂) * (L * Real.log (1 + L) / T)) := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = A * max K₁ (16 * c / π * K₂) *
          (perronEdge L T M + perronEdge L T N + L * Real.log (1 + L) / T) := by ring


end LeanProofs.IntegerPoints
