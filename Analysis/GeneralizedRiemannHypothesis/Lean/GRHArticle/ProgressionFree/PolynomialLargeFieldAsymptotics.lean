import GRHArticle.ProgressionFree.PolynomialLargeFieldGap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Asymptotics of the large-field degree-benchmark gap

The numerical error tends to zero after multiplication by any fixed
power of the field size. The logarithmic ratio has a uniform upper bound
tending to `-1`.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology

/-- The numerical error in the published large-field comparison. -/
noncomputable def polynomialLargeFieldError (q : ℕ) : ℝ :=
  (2*(q : ℝ)+1)*(q : ℝ)⁻¹^(q-14)

/-- Any fixed-power rescaling of the error is eventually at most `3/q`. -/
theorem polynomialLargeField_scaledGap_le {q m : ℕ} {x : ℝ}
    (hq : m+16 ≤ q) (hx : x ≤ polynomialLargeFieldError q) :
    (q : ℝ)^m*x ≤ 3*(q : ℝ)⁻¹ := by
  let Q := (q : ℝ)
  have hQ1 : 1 ≤ Q := by dsimp [Q]; exact_mod_cast (show 1 ≤ q by omega)
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  have hp : Q⁻¹^(q-14) ≤ Q⁻¹^(m+2) :=
    pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hQ1) (by omega)
  have hlin : 2*Q+1 ≤ 3*Q := by linarith
  change Q^m*x ≤ 3*Q⁻¹
  calc
    _ ≤ Q^m*((2*Q+1)*Q⁻¹^(q-14)) := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ Q^m*((3*Q)*Q⁻¹^(m+2)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul hlin hp (by positivity) (by positivity)) (by positivity)
    _ = _ := by
      rw [pow_add (Q⁻¹) m 2, inv_pow, pow_two (Q⁻¹)]
      field_simp [hQ0.ne']

/-- Pointwise logarithmic bound for every positive gap below the numerical
large-field estimate. -/
theorem polynomialLargeField_logRatio_le {q : ℕ} {x : ℝ}
    (hq : 16 ≤ q) (hx : 0 < x) (h : x ≤ polynomialLargeFieldError q) :
    Real.log x/((q : ℝ)*Real.log (q : ℝ)) ≤ -1+16/(q : ℝ) := by
  let Q := (q : ℝ)
  have hQ3 : 3 ≤ Q := by dsimp [Q]; exact_mod_cast (show 3 ≤ q by omega)
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 < Q := by linarith
  have hquad : 2*Q+1 ≤ Q^2 := by
    have h' := mul_nonneg hQ0.le (sub_nonneg.mpr hQ3)
    nlinarith only [h',hQ3]
  have h' : x ≤ Q^2 * Q⁻¹^(q-14) :=
    h.trans (mul_le_mul_of_nonneg_right hquad (by positivity))
  have H := Real.log_le_log hx h'
  have hsub : ((q-14 : ℕ) : ℝ) = Q-14 := by
    rw [Nat.cast_sub (show 14 ≤ q by omega)]
    norm_num [Q]
  rw [Real.log_mul (pow_ne_zero _ hQ0.ne') (pow_ne_zero _ (inv_ne_zero hQ0.ne')),
    Real.log_pow, Real.log_pow, Real.log_inv, hsub] at H
  change Real.log x/(Q*Real.log Q) ≤ -1+16/Q
  apply (div_le_iff₀ (mul_pos hQ0 (Real.log_pos hQ1))).mpr
  refine H.trans_eq ?_
  field_simp [hQ0.ne']
  ring

variable {ι : Type*} {l : Filter ι} {q : ι → ℕ} {x : ι → ℝ}

private theorem tendsto_largeField_inv (hq : Tendsto q l atTop) :
    Tendsto (fun i ↦ (q i : ℝ)⁻¹) l (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hq)

/-- Any nonnegative gaps bounded by the large-field error vanish after every
fixed natural-power rescaling along any field-size filter. -/
theorem tendsto_polynomialLargeField_scaledGap (hq : Tendsto q l atTop)
    (hx : ∀ᶠ i in l, 0 ≤ x i ∧ x i ≤ polynomialLargeFieldError (q i)) (m : ℕ) :
    Tendsto (fun i ↦ (q i : ℝ)^m * x i) l (𝓝 0) := by
  have hupper := (tendsto_largeField_inv hq).const_mul (3 : ℝ)
  rw [mul_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact hx.mono (fun i hi ↦ mul_nonneg (by positivity) hi.1)
  · filter_upwards [hx, (tendsto_atTop.mp hq) (m+16)] with i hi hm
    exact polynomialLargeField_scaledGap_le hm hi.2

private theorem tendsto_largeField_logUpper (hq : Tendsto q l atTop) :
    Tendsto (fun i ↦ (-1 : ℝ)+16/(q i : ℝ)) l (𝓝 (-1)) := by
  simpa only [div_eq_mul_inv, mul_zero, add_zero] using
    ((tendsto_largeField_inv hq).const_mul (16 : ℝ)).const_add (-1)

/-- The eventual formulation of the logarithmic upper limit. -/
theorem eventually_polynomialLargeField_logRatio_lt (hq : Tendsto q l atTop)
    (hx : ∀ᶠ i in l, 0 < x i ∧ x i ≤ polynomialLargeFieldError (q i)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, Real.log (x i)/((q i : ℝ)*Real.log (q i : ℝ)) < -1+ε := by
  have hb := (tendsto_largeField_logUpper hq).eventually_lt_const (lt_add_of_pos_right (-1) hε)
  filter_upwards [hx, (tendsto_atTop.mp hq) 16, hb] with i hi hqi hbi
  exact (polynomialLargeField_logRatio_le hqi hi.1 hi.2).trans_lt hbi

/-- The extended-real upper limit is at most `-1`. This also allows the
logarithmic ratio to tend to negative infinity. -/
theorem limsup_polynomialLargeField_logRatio_le (hq : Tendsto q l atTop)
    (hx : ∀ᶠ i in l, 0 < x i ∧ x i ≤ polynomialLargeFieldError (q i)) :
    limsup (fun i ↦ ((Real.log (x i)/((q i : ℝ)*Real.log (q i : ℝ)) : ℝ) : EReal)) l ≤
      ((-1 : ℝ) : EReal) := by
  by_cases hl : l.NeBot
  · letI := hl
    let b (i : ι) := ((-1+16/(q i : ℝ) : ℝ) : EReal)
    have ht : Tendsto b l (𝓝 ((-1 : ℝ) : EReal)) :=
      continuous_coe_real_ereal.continuousAt.tendsto.comp (tendsto_largeField_logUpper hq)
    let a (i : ι) := ((Real.log (x i)/((q i : ℝ)*Real.log (q i : ℝ)) : ℝ) : EReal)
    have hle : a ≤ᶠ[l] b := by
      filter_upwards [hx, (tendsto_atTop.mp hq) 16] with i hi hqi
      exact EReal.coe_le_coe_iff.mpr (polynomialLargeField_logRatio_le hqi hi.1 hi.2)
    have ha : l.IsCoboundedUnder (· ≤ ·) a :=
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun i ↦ show (⊥ : EReal) ≤ a i from bot_le)).isCoboundedUnder_le
    have hb : l.IsBoundedUnder (· ≤ ·) b :=
      isBoundedUnder_of_eventually_le (Eventually.of_forall fun i ↦ show b i ≤ (⊤ : EReal) from le_top)
    rw [← ht.limsup_eq]
    exact limsup_le_limsup hle ha hb
  · simp [not_neBot.mp hl]

section FieldFamily

variable (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]

private theorem fieldFamily_largeField_error (hq : Tendsto (fun i ↦ Fintype.card (F i)) l atTop) :
    ∀ᶠ i in l, 0 < polynomialRatioDensitySupremum (F i) - polynomialDegreeBenchmark (F i) ∧
      polynomialRatioDensitySupremum (F i) - polynomialDegreeBenchmark (F i) ≤
        polynomialLargeFieldError (Fintype.card (F i)) := by
  filter_upwards [(tendsto_atTop.mp hq) 16] with i hi
  exact polynomialRatioDensitySupremum_largeField (F i) hi

/-- The polynomial-ratio density supremum and the benchmark agree to
all fixed orders as the finite-field cardinalities tend to infinity. -/
theorem tendsto_polynomialRatioDensityGap_scaled
    (hq : Tendsto (fun i ↦ Fintype.card (F i)) l atTop) (m : ℕ) :
    Tendsto (fun i ↦ (Fintype.card (F i) : ℝ)^m *
      (polynomialRatioDensitySupremum (F i) - polynomialDegreeBenchmark (F i))) l (𝓝 0) :=
  tendsto_polynomialLargeField_scaledGap hq ((fieldFamily_largeField_error F hq).mono
    (fun _ hi ↦ ⟨hi.1.le,hi.2⟩)) m

/-- The extended-real upper limit of the actual logarithmic gap quotient. -/
theorem limsup_polynomialRatioDensityGap_logRatio_le
    (hq : Tendsto (fun i ↦ Fintype.card (F i)) l atTop) :
    limsup (fun i ↦ ((Real.log (polynomialRatioDensitySupremum (F i) - polynomialDegreeBenchmark (F i)) /
      ((Fintype.card (F i) : ℝ)*Real.log (Fintype.card (F i) : ℝ)) : ℝ) : EReal)) l ≤ ((-1 : ℝ) : EReal) :=
  limsup_polynomialLargeField_logRatio_le hq (fieldFamily_largeField_error F hq)

end FieldFamily
end GRHArticle.ProgressionFree
