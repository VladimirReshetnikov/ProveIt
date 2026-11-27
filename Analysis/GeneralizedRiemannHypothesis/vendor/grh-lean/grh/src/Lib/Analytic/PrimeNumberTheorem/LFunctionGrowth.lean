import Lib.Analytic.EntireLFunction

/-!
# Growth of Dirichlet L-functions near the line `re s = 1`

Let `χ` be a character modulo `N`, and let `𝖿_χ(s)` (`regularL χ s`) be `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. Partial summation gives `|𝖿_χ(s)| ≤ 1 + 4 N |s|` in
`re s ≥ 1 / 2`, and the three-lines theorem improves this to `|𝖿_χ(s)| ≤ l²` for `re s ≥ 1 - 1 / l`
and `|s| ≤ 3 e^l`, whenever `l ≥ 10¹⁰` and `N ≤ e^l`.

Notions from other files:
* `entireL χ`: the entire function equal to `L(s, χ)` if `χ` is not principal, and to the
  continuation of `(s - 1) L(s, χ)` if it is.

## Relation to the literature

Known result: the bound `L(s, χ) ≪ log (N |s|)` near `re s = 1` and away from the pole. It is proved
here for `𝖿_χ` and with a square in place of the first power. Source: Montgomery and Vaughan,
Multiplicative Number Theory I, 2007, Lemma 10.15.
-/

noncomputable section

open Complex Real Set Filter Topology MeasureTheory Metric Asymptotics DirichletCharacter
  HadamardThreeLines
open scoped Classical

namespace New

section Transform

variable {r : ℝ → ℂ} {C : ℝ} {s : ℂ}

/-- If `|r| ≤ C` on `(1, ∞)`, then the integrand of `∫₁^∞ r(t) t ^ (-s - 1) dt` is dominated by
`C t ^ (-re s - 1)`. -/
lemma norm_mul_cpow_neg_add_one_le (h_bound : ∀ t : ℝ, 1 < t → ‖r t‖ ≤ C) {t : ℝ} (ht : 1 < t) :
    ‖r t * t ^ (-(s + 1))‖ ≤ C * t ^ (-(s.re + 1)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (one_pos.trans ht), neg_re, add_re, one_re]
  exact mul_le_mul_of_nonneg_right (h_bound t ht) (by positivity)

/-- For a bounded measurable `r`, the integral `∫₁^∞ r(t) t ^ (-s - 1) dt` converges in
`re s > 0`. -/
lemma integrableOn_mul_cpow_of_bounded (hr : Measurable r) (h_bound : ∀ t : ℝ, 1 < t → ‖r t‖ ≤ C)
    (hs : 0 < s.re) : IntegrableOn (fun t : ℝ ↦ r t * t ^ (-(s + 1))) (Ioi 1) := by
  have h_exp : -(s.re + 1) < -1 := by linarith
  exact ((integrableOn_Ioi_rpow_of_lt h_exp one_pos).const_mul C).mono' (by fun_prop)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ↦ norm_mul_cpow_neg_add_one_le h_bound)

/-- If `|r| ≤ C` on `(1, ∞)`, then `|∫₁^∞ r(t) t ^ (-s - 1) dt| ≤ C / re s` for `re s > 0`. -/
lemma norm_integral_mul_cpow_le (h_bound : ∀ t : ℝ, 1 < t → ‖r t‖ ≤ C) (hs : 0 < s.re) :
    ‖∫ t : ℝ in Ioi (1 : ℝ), r t * t ^ (-(s + 1))‖ ≤ C / s.re := by
  have h_exp : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), C * t ^ (-(s.re + 1)) :=
      norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt h_exp one_pos).const_mul C)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ↦ norm_mul_cpow_neg_add_one_le h_bound)
    _ = C / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt h_exp one_pos, Real.one_rpow, neg_add,
        neg_add_cancel_right, neg_div_neg_eq, mul_one_div]

/-- For a bounded measurable `r`, the integral `∫₁^∞ r(t) t ^ (-s - 1) dt` is holomorphic in
`re s > 0`. -/
lemma differentiableAt_integral_mul_cpow (hr : Measurable r)
    (h_bound : ∀ t : ℝ, 1 < t → ‖r t‖ ≤ C) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦ ∫ t : ℝ in Ioi (1 : ℝ), r t * t ^ (-(z + 1))) s := by
  -- The integral is the Mellin transform at `-z` of `r` cut off below `1`. This function is
  -- bounded and vanishes near `0`, so its transform is holomorphic to the left of `0`.
  let f : ℝ → ℂ := (Ioi 1).indicator r
  have h_mellin (z : ℂ) : ∫ t in Ioi (1 : ℝ), r t * t ^ (-(z + 1)) = mellin f (-z) := by
    rw [mellin, ← inter_eq_right.2 (Ioi_subset_Ioi zero_le_one),
      ← setIntegral_indicator measurableSet_Ioi]
    simp [f, indicator, mul_comm, sub_eq_add_neg, add_comm]
  have f_bound (t : ℝ) : ‖f t‖ ≤ |C| := by
    by_cases ht : 1 < t <;> simp [f, ht, (h_bound t _).trans (le_abs_self C)]
  have f_loc : LocallyIntegrable f :=
    (locallyIntegrable_const |C|).mono (hr.indicator measurableSet_Ioi).aestronglyMeasurable
      (.of_forall fun t ↦ by simpa using f_bound t)
  have f_top : f =O[atTop] fun t : ℝ ↦ t ^ (-(0 : ℝ)) :=
    .of_bound |C| (.of_forall fun t ↦ by simpa using f_bound t)
  have f_bot : f =O[𝓝[>] 0] fun t : ℝ ↦ t ^ (-(-s.re - 1)) := by
    refine (isBigO_zero _ _).congr' ?_ .rfl
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)] with t (ht : t < 1)
    simp [f, ht.le]
  simp only [h_mellin]
  exact (mellin_differentiableAt_of_isBigO_rpow (f_loc.locallyIntegrableOn _) f_top
    (by simpa : (-s).re < 0) f_bot (by simp)).comp s differentiableAt_id.neg

end Transform

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}

/-- The mean value of a Dirichlet character over the classes modulo `N`. -/
def charMean : ℂ := (∑ a : ZMod N, χ a) / N

/-- The mean value of a Dirichlet character has absolute value at most `1`. -/
lemma norm_charMean_le_one : ‖charMean χ‖ ≤ 1 := by
  have h_sum : ‖∑ a : ZMod N, χ a‖ ≤ N := by
    simpa using norm_sum_le_of_le Finset.univ fun a _ ↦ χ.norm_le_one a
  rw [charMean, norm_div, Complex.norm_natCast]
  exact div_le_one_of_le₀ h_sum N.cast_nonneg

/-- The mean value of a nonprincipal Dirichlet character is `0`. -/
lemma charMean_eq_zero (hχ : χ ≠ 1) : charMean χ = 0 := by
  rw [charMean, MulChar.sum_eq_zero_of_ne_one hχ, zero_div]

/-- A sum of `χ` over `N` consecutive integers is `N` times the mean value `charMean χ` of `χ`,
that is, the sum over all classes modulo `N`. -/
lemma sum_range_char_add (M : ℕ) :
    ∑ n ∈ Finset.range N, χ (M + n : ℕ) = N * charMean χ := by
  rw [charMean, mul_div_cancel₀ _ (NeZero.natCast_ne N ℂ),
    ← Equiv.sum_comp (Equiv.addLeft (M : ZMod N))]
  -- `n ↦ n mod N` is a bijection from `{0, …, N - 1}` to `ZMod N`.
  have val_natCast : ∀ n ∈ Finset.range N, (n : ZMod N).val = n :=
    fun n hn ↦ ZMod.val_natCast_of_lt (Finset.mem_range.1 hn)
  exact Finset.sum_nbij' (fun n ↦ (n : ZMod N)) ZMod.val (by simp) (by simp [ZMod.val_lt])
    val_natCast (fun a _ ↦ ZMod.natCast_zmod_val a) (by simp)

/-- The sum of the values of `χ` up to `x` differs from `x` times the mean value `charMean χ` by at
most `2 N`. -/
lemma norm_sum_char_sub_le {x : ℝ} (hx : 0 ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n - charMean χ * x‖ ≤ 2 * N := by
  -- The sums `S M` of `χ` less its mean have period `N`, so fewer than `N` terms count.
  let S (M : ℕ) : ℂ := ∑ n ∈ Finset.range M, (χ (1 + n : ℕ) - charMean χ)
  have S_periodic : Function.Periodic S N := by
    intro M
    -- The `N` terms by which `S (M + N)` exceeds `S M` add up to `0`.
    simp only [S, Finset.sum_range_add, add_eq_left, ← add_assoc]
    rw [Finset.sum_sub_distrib, sum_range_char_add, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sub_self]
  have S_le (M : ℕ) : ‖S M‖ ≤ 2 * M := by
    have term_le (n : ℕ) : ‖χ (1 + n : ℕ) - charMean χ‖ ≤ 2 :=
      (norm_sub_le_of_le (χ.norm_le_one _) (norm_charMean_le_one χ)).trans_eq one_add_one_eq_two
    exact (norm_sum_le_of_le (Finset.range M) fun n _ ↦ term_le n).trans_eq (by simp [mul_comm])
  have h_mod : ((⌊x⌋₊ % N : ℕ) : ℝ) + 1 ≤ N := mod_cast Nat.mod_lt _ (NeZero.pos N)
  have h_split : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n - charMean χ * x =
      S ⌊x⌋₊ - charMean χ * (x - ⌊x⌋₊ : ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [S, Finset.sum_sub_distrib]
    ring
  calc
    _ ≤ ‖S (⌊x⌋₊ % N)‖ + ‖charMean χ‖ * |x - ⌊x⌋₊| := by
      rw [h_split, S_periodic.map_mod_nat, ← Real.norm_eq_abs, ← norm_real, ← norm_mul]
      exact norm_sub_le _ _
    _ ≤ 2 * (⌊x⌋₊ % N : ℕ) + 1 * 1 := by
      gcongr
      exacts [S_le _, norm_charMean_le_one χ, Nat.abs_sub_floor_le hx]
    _ ≤ 2 * N := by linarith

omit [NeZero N] in
/-- If `re s ≥ 1 + 1 / A` with `A > 0`, then `|L(s, χ)| ≤ 1 + A`, since the Dirichlet series of
`χ` is dominated by `ζ(re s)`. -/
lemma norm_LSeries_char_le {A : ℝ} (hA : 0 < A) (hs : 1 + 1 / A ≤ s.re) :
    ‖LSeries (fun n : ℕ ↦ χ n) s‖ ≤ 1 + A := by
  have hs_one : 1 < s.re := by linarith [one_div_pos.2 hA]
  have h_summable : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ s.re :=
    Real.summable_one_div_nat_rpow.2 hs_one
  have term_le (n : ℕ) : ‖LSeries.term (χ ·) s n‖ ≤ 1 / (n : ℝ) ^ s.re := by
    rw [LSeries.norm_term_eq]
    split_ifs
    · positivity
    · exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  -- `ζ(σ) - 1 / (σ - 1) = 1 - σ T` with `T ≥ 0`
  have zeta_le : ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s.re ≤ 1 + 1 / (s.re - 1) := by
    have h_nonneg : 0 ≤ s.re * ZetaAsymptotics.termTSum s.re :=
      mul_nonneg (by linarith) (tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg _ _)
    linarith [ZetaAsymptotics.zeta_limit_aux1 hs_one]
  calc
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := tsum_of_norm_bounded h_summable.hasSum term_le
    _ = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s.re := by
      rw [h_summable.tsum_eq_zero_add]
      simp [Real.zero_rpow (one_pos.trans hs_one).ne']
    _ ≤ 1 + 1 / (s.re - 1) := zeta_le
    _ ≤ 1 + A := by linarith [(one_div_le hA (sub_pos.2 hs_one)).1 (by linarith)]

/-- `𝖿_χ(s)` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal. The entire function `entireL χ`
has the factor `s - 1` in that case; dividing by `s` keeps the size of `L(s, χ)` for large `|s|`. -/
def regularL (s : ℂ) : ℂ := entireL χ s / if χ = 1 then s else 1

/-- `𝖿_χ` (`regularL χ`: `L(s, χ)`, times `(s - 1) / s` if `χ` is principal) is holomorphic in
`re s > 0`. -/
lemma differentiableAt_regularL (hs : 0 < s.re) : DifferentiableAt ℂ (regularL χ) s := by
  have h_denom_diff : DifferentiableAt ℂ (fun z : ℂ ↦ if χ = 1 then z else 1) s := by
    split_ifs <;> fun_prop
  have h_denom_ne : (if χ = 1 then s else 1) ≠ 0 := by
    split_ifs
    exacts [ne_zero_of_re_pos hs, one_ne_zero]
  exact (analyticAt_entireL χ s).differentiableAt.div h_denom_diff h_denom_ne

/-- In `re s > 1` the regularised function `𝖿_χ` (`regularL χ`) is `L(s, χ) (s - δ) / s`, with
`δ = 1` if `χ` is principal and `δ = 0` otherwise. -/
lemma regularL_eq (hs : 1 < s.re) :
    regularL χ s = LSeries (fun n : ℕ ↦ χ n) s / s * (s - if χ = 1 then 1 else 0) := by
  have hs_zero : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  rw [regularL, entireL, ← χ.LFunction_eq_LSeries hs]
  split_ifs with hχ
  · rw [hχ, LFunctionTrivChar₁, Function.update_of_ne (ne_of_apply_ne re hs.ne')]
    ring
  · field

/-- `|s - δ| ≤ |s|` in `re s ≥ 1 / 2`, where `δ` is `1` or `0` as the proposition `p` holds or
not (in the uses, `p` says that a character is principal). -/
lemma norm_sub_ite_le {p : Prop} [Decidable p] (hs : 1 / 2 ≤ s.re) :
    ‖s - if p then 1 else 0‖ ≤ ‖s‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  split_ifs
  · simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, one_re, one_im]
    -- For `δ = 1` this is `(re s - 1)² ≤ (re s)²`.
    linarith
  · simp

/-- Partial summation: `|𝖿_χ(s)| ≤ 1 + 4 N |s|` in `re s ≥ 1 / 2`, where `𝖿_χ` (`regularL χ`) is
`L(s, χ)`, times `(s - 1) / s` if `χ` is principal, and `N` is the modulus of `χ`. -/
lemma norm_regularL_le_linear (hs : 1 / 2 ≤ s.re) : ‖regularL χ s‖ ≤ 1 + 4 * N * ‖s‖ := by
  -- Write `∑_{n ≤ t} χ(n) = κ t + r(t)` with `|r| ≤ 2 N`. Then `𝖿_χ = κ + (s - δ) Φ`, where
  -- `Φ(s) = ∫₁^∞ r(t) t ^ (-s - 1) dt`, first in `re s > 1` and then, by the identity theorem,
  -- in `re s > 0`.
  let κ : ℂ := charMean χ
  let δ : ℂ := if χ = 1 then 1 else 0
  let r (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n - κ * t
  let Φ (z : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), r t * t ^ (-(z + 1))
  have r_meas : Measurable r :=
    ((measurable_of_countable fun M : ℕ ↦ ∑ n ∈ Finset.Icc 1 M, χ n).comp
      Nat.measurable_floor).sub (by fun_prop)
  have r_le (t : ℝ) (ht : 1 < t) : ‖r t‖ ≤ 2 * N := norm_sum_char_sub_le χ (by linarith)
  have series_eq (z : ℂ) (hz : 1 < z.re) :
      LSeries (fun n : ℕ ↦ χ n) z = z * (Φ z + κ / (z - 1)) := by
    have h_exp : (-z).re < -1 := by simpa
    have h_sum : (fun M : ℕ ↦ ∑ n ∈ Finset.Icc 1 M, ‖χ n‖) =O[atTop]
        fun M : ℕ ↦ (M : ℝ) ^ (1 : ℝ) := by
      refine isBigO_of_le _ fun M ↦ ?_
      have sum_le : ∑ n ∈ Finset.Icc 1 M, ‖χ n‖ ≤ M := by
        simpa using (Finset.Icc 1 M).sum_le_card_nsmul _ 1 fun n _ ↦ χ.norm_le_one n
      simpa [abs_of_nonneg, Finset.sum_nonneg] using sum_le
    have h_main : κ / (z - 1) = ∫ t in Ioi (1 : ℝ), κ * t ^ (-z) := by
      rw [integral_const_mul, integral_Ioi_cpow_of_lt h_exp one_pos, ofReal_one, one_cpow,
        neg_add_eq_sub, ← neg_sub z, neg_div_neg_eq, mul_one_div]
    have h_int_r : IntegrableOn (fun t : ℝ ↦ r t * t ^ (-(z + 1))) (Ioi 1) :=
      integrableOn_mul_cpow_of_bounded r_meas r_le (by linarith)
    have h_int_main : IntegrableOn (fun t : ℝ ↦ κ * t ^ (-z)) (Ioi 1) :=
      (integrableOn_Ioi_cpow_of_lt h_exp one_pos).const_mul κ
    rw [LSeries_eq_mul_integral' _ zero_le_one hz h_sum, h_main,
      ← integral_add h_int_r h_int_main]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦ ?_
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (one_pos.trans ht).ne'
    simp only [r, neg_add, cpow_add _ _ ht_ne, cpow_neg_one]
    field
  have far_right (z : ℂ) (hz : 1 < z.re) : regularL χ z = κ + Φ z * (z - δ) := by
    have hz_one : z - 1 ≠ 0 := ne_zero_of_re_pos (by simpa using hz)
    rw [regularL_eq χ hz, series_eq z hz, mul_div_cancel_left₀ _ (ne_zero_of_re_pos (by linarith))]
    by_cases hχ : χ = 1
    · simp only [δ, ite_eq_left hχ]
      field
    · simp [δ, κ, ite_eq_right hχ, charMean_eq_zero χ hχ]
  have identity : EqOn (regularL χ) (fun z ↦ κ + Φ z * (z - δ)) {z : ℂ | 0 < z.re} := by
    have analytic {F : ℂ → ℂ} (hF : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F z) :
        AnalyticOnNhd ℂ F {z : ℂ | 0 < z.re} :=
      DifferentiableOn.analyticOnNhd (fun z hz ↦ (hF z hz).differentiableWithinAt) (isOpen_re_gt 0)
    have h_right : AnalyticOnNhd ℂ (fun z ↦ κ + Φ z * (z - δ)) {z : ℂ | 0 < z.re} :=
      analytic fun z hz ↦
        ((differentiableAt_integral_mul_cpow r_meas r_le hz).mul (by fun_prop)).const_add κ
    have h_near_two : regularL χ =ᶠ[𝓝 2] fun z ↦ κ + Φ z * (z - δ) :=
      eventually_of_mem ((isOpen_re_gt 1).mem_nhds (by simp)) far_right
    exact (analytic fun z ↦ differentiableAt_regularL χ).eqOn_of_preconnected_of_eventuallyEq
      h_right (convex_halfSpace_re_gt 0).isPreconnected (by simp) h_near_two
  have hs_pos : 0 < s.re := by linarith
  calc
    ‖regularL χ s‖ ≤ ‖κ‖ + ‖Φ s‖ * ‖s - δ‖ := by
      rw [identity hs_pos, ← norm_mul]
      exact norm_add_le _ _
    _ ≤ 1 + 2 * N / s.re * ‖s‖ := by
      gcongr
      exacts [norm_charMean_le_one χ, norm_integral_mul_cpow_le r_le hs_pos, norm_sub_ite_le hs]
    _ ≤ 1 + 2 * N / (1 / 2) * ‖s‖ := by gcongr
    _ = 1 + 4 * N * ‖s‖ := by ring

/-- For `l ≥ 1` and `re s > 1`, at distance at least `1 / l` from `1` if `χ` is principal, we have
`|L(s, χ)| ≤ 2 l |𝖿_χ(s)|`, where `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times `(s - 1) / s` if `χ` is
principal. -/
lemma norm_LSeries_le_mul_norm_regularL (hs : 1 < s.re) (hl : 1 ≤ l)
    (h_far : χ = 1 → 1 / l ≤ ‖s - 1‖) :
    ‖LSeries (fun n : ℕ ↦ χ n) s‖ ≤ 2 * l * ‖regularL χ s‖ := by
  have hs_norm : 1 < ‖s‖ := hs.trans_le (re_le_norm s)
  have norm_le : ‖s‖ ≤ 2 * l * ‖s - if χ = 1 then 1 else 0‖ := by
    split_ifs with hχ
    · have h_one : 1 ≤ ‖s - 1‖ * l := (div_le_iff₀ (by linarith)).1 (h_far hχ)
      nlinarith [norm_nonneg (s - 1), norm_le_norm_sub_add s 1, norm_one (α := ℂ)]
    · simpa using le_mul_of_one_le_left (norm_nonneg s) (by linarith : 1 ≤ 2 * l)
  calc
    ‖LSeries (χ ·) s‖ = ‖LSeries (χ ·) s‖ / ‖s‖ * ‖s‖ := by field
    _ ≤ ‖LSeries (χ ·) s‖ / ‖s‖ * (2 * l * ‖s - if χ = 1 then 1 else 0‖) := by gcongr
    _ = 2 * l * ‖regularL χ s‖ := by simp [regularL_eq χ hs]; ring

/-- If `l ≥ 10¹⁰` and the modulus `N` is at most `e^l`, then `|𝖿_χ(s)| ≤ l²` for
`re s ≥ 1 - 1 / l` and `|s| ≤ 3 e^l`. Here `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. -/
lemma norm_regularL_le_sq (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) (h_re : 1 - 1 / l ≤ s.re)
    (h_norm : ‖s‖ ≤ 3 * rexp l) : ‖regularL χ s‖ ≤ l ^ 2 := by
  -- Apply the three-lines theorem to `g(z) = 𝖿_χ(z) / (z - s + 2)` on the strip
  -- `a ≤ re z ≤ a + 1 / 3` whose right edge lies at `re s + 2 / l ≥ 1 + 1 / l`. The left edge,
  -- where `|g| ≤ e^(3 l)`, has the weight `6 / l` at `s`. The denominator makes `g` bounded; it
  -- has modulus at least `1` on the strip and is `2` at `s`.
  have inv_pos : 0 < 1 / l := by positivity
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have exp_ge : l + 1 ≤ rexp l := add_one_le_exp l
  set a : ℝ := s.re + 2 * (1 / l) - 1 / 3 with ha
  let g (z : ℂ) : ℂ := regularL χ z / (z - (s - 2))
  have denom_ge (z : ℂ) (hz : a ≤ z.re) : 1 ≤ ‖z - (s - 2)‖ :=
    le_trans (by simp; linarith) (re_le_norm _)
  have g_le_exp_cube (z : ℂ) (hz : a ≤ z.re) : ‖g z‖ ≤ rexp l ^ 3 := by
    have h_denom : 1 ≤ ‖z - (s - 2)‖ := denom_ge z hz
    have hz_norm : ‖z‖ ≤ 4 * rexp l * ‖z - (s - 2)‖ := by
      nlinarith [norm_le_norm_sub_add z (s - 2), norm_sub_le s 2, Complex.norm_two]
    rw [norm_div, div_le_iff₀ (by linarith)]
    calc
      ‖regularL χ z‖ ≤ 1 + 4 * N * ‖z‖ := norm_regularL_le_linear χ (by linarith)
      _ ≤ 1 * ‖z - (s - 2)‖ + 4 * rexp l * (4 * rexp l * ‖z - (s - 2)‖) := by
        gcongr
        linarith
      _ = (1 + 16 * rexp l ^ 2) * ‖z - (s - 2)‖ := by ring
      _ ≤ rexp l ^ 3 * ‖z - (s - 2)‖ := by
        gcongr
        nlinarith [sq_nonneg (rexp l), mul_le_mul exp_ge exp_ge]
  have right_edge (z : ℂ) (hz : z.re = a + 1 / 3) : ‖g z‖ ≤ 1 + l := by
    have hz_norm : 0 < ‖z‖ := by linarith [re_le_norm z]
    calc
      ‖g z‖ ≤ ‖regularL χ z‖ :=
        (norm_div _ _).trans_le (div_le_self (norm_nonneg _) (denom_ge z (by linarith)))
      _ ≤ ‖LSeries (χ ·) z‖ / ‖z‖ * ‖z‖ := by
        rw [regularL_eq χ (by linarith), norm_mul, norm_div]
        gcongr
        exact norm_sub_ite_le (by linarith)
      _ = ‖LSeries (χ ·) z‖ := div_mul_cancel₀ _ hz_norm.ne'
      _ ≤ 1 + l := by
        have h_re_right : 1 + 1 / l ≤ z.re := by linarith
        exact norm_LSeries_char_le χ (by linarith) h_re_right
  have g_diff : DiffContOnCl ℂ g (verticalStrip a (a + 1 / 3)) := by
    refine DifferentiableOn.diffContOnCl fun z hz ↦ ?_
    rw [verticalStrip, closure_preimage_re, closure_Ioo (by linarith)] at hz
    obtain ⟨hz_left, -⟩ : a ≤ z.re ∧ z.re ≤ a + 1 / 3 := hz
    have hz_pos : 0 < z.re := by linarith
    have h_denom : z - (s - 2) ≠ 0 := norm_pos_iff.1 (one_pos.trans_le (denom_ge z hz_left))
    exact ((differentiableAt_regularL χ hz_pos).fun_div (by fun_prop)
      h_denom).differentiableWithinAt
  have weight : (s.re - a) / (a + 1 / 3 - a) = 1 - 6 / l := by rw [ha]; ring
  have three_lines : ‖g s‖ ≤ (rexp l ^ 3) ^ (1 - (1 - 6 / l)) * (1 + l) ^ (1 - 6 / l) := by
    have hs_strip : s ∈ verticalClosedStrip a (a + 1 / 3) := ⟨by linarith, by linarith⟩
    have g_bdd : BddAbove ((norm ∘ g) '' verticalClosedStrip a (a + 1 / 3)) :=
      ⟨rexp l ^ 3, forall_mem_image.2 fun z ⟨hz, _⟩ ↦ g_le_exp_cube z hz⟩
    rw [← weight]
    exact norm_le_interp_of_mem_verticalClosedStrip' (by linarith) hs_strip g_diff g_bdd
      (fun z hz ↦ g_le_exp_cube z hz.ge) right_edge
  have left_factor : (rexp l ^ 3) ^ (1 - (1 - 6 / l)) ≤ 3 ^ 18 := by
    have h_exp : ((3 : ℕ) * l) * (1 - (1 - 6 / l)) = (18 : ℕ) * 1 := by field
    rw [← Real.exp_nat_mul, ← Real.exp_mul, h_exp, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (exp_nonneg 1) exp_one_lt_three.le 18
  have right_factor : (1 + l) ^ (1 - 6 / l) ≤ 1 + l :=
    rpow_le_self_of_one_le (by linarith) (sub_le_self 1 (by positivity))
  calc
    ‖regularL χ s‖ = 2 * ‖g s‖ := by simp [g, mul_div_cancel₀]
    _ ≤ 2 * (3 ^ 18 * (1 + l)) := by grw [three_lines, left_factor, right_factor]
    _ ≤ l ^ 2 := by nlinarith

/-- Cauchy's estimate: if `l ≥ 10¹⁰` and the modulus `N` is at most `e^l`, then `|𝖿_χ'(s)| ≤ 2 l³`
for `re s ≥ 1 - 1 / (2 l)` and `|s| ≤ 2 e^l`. Here `𝖿_χ` (`regularL χ`) is `L(s, χ)`, times
`(s - 1) / s` if `χ` is principal. -/
lemma norm_deriv_regularL_le (hl : 10 ^ 10 ≤ l) (hN : N ≤ rexp l) (h_re : 1 - 1 / l / 2 ≤ s.re)
    (h_norm : ‖s‖ ≤ 2 * rexp l) : ‖deriv (regularL χ) s‖ ≤ 2 * l ^ 3 := by
  have inv_le : 1 / l ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have disc (z : ℂ) (hz : z ∈ closedBall s (1 / l / 2)) :
      1 - 1 / l ≤ z.re ∧ ‖z‖ ≤ 3 * rexp l := by
    rw [mem_closedBall_iff_norm] at hz
    exact ⟨by linarith [neg_le_of_abs_le (abs_re_le_norm (z - s)), sub_re z s],
      by linarith [norm_le_norm_sub_add z s, add_one_le_exp l]⟩
  have h_diff : DiffContOnCl ℂ (regularL χ) (ball s (1 / l / 2)) :=
    DifferentiableOn.diffContOnCl_ball (fun z hz ↦ (differentiableAt_regularL χ
      (by linarith [(disc z hz).1])).differentiableWithinAt) subset_rfl
  have h_sphere (z : ℂ) (hz : z ∈ sphere s (1 / l / 2)) : ‖regularL χ z‖ ≤ l ^ 2 := by
    obtain ⟨hz_re, hz_norm⟩ := disc z (sphere_subset_closedBall hz)
    exact norm_regularL_le_sq χ hl hN hz_re hz_norm
  calc
    _ ≤ l ^ 2 / (1 / l / 2) :=
      norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) h_diff h_sphere
    _ = 2 * l ^ 3 := by field

end New

end
