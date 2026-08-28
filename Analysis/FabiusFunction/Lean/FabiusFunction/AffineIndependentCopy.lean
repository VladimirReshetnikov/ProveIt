import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Contractive affine independent-copy laws

This module isolates a measure-theoretic uniqueness principle for affine
distributional equations in a real inner-product space.  If `D` has law
`rho`, `X` has law `mu`, and the two variables are independent, then

`digit D + q • X`

has law `affineIndependentCopyLaw rho digit q mu`.  For `|q| < 1`, this
operator has at most one probability fixed point.  The proof uses only
characteristic functions: their common digit factor has norm at most one,
while the arguments `q ^ n • t` tend to zero.  No support, absolute
continuity, or moment hypothesis is involved.
-/

set_option autoImplicit false

open Filter MeasureTheory Topology

namespace ProbabilityTheory

noncomputable section

/-- The law of `digit D + q • X` when `D` and `X` are independent with laws
`rho` and `mu`, respectively. -/
noncomputable def affineIndependentCopyLaw
    {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (rho : Measure D) (digit : D → E) (q : ℝ)
    (mu : Measure E) : Measure E :=
  (rho.map digit) ∗ (mu.map (q • ·))

/-- The affine independent-copy operator preserves probability measures. -/
theorem affineIndependentCopyLaw_isProbabilityMeasure
    {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {rho : Measure D} [IsProbabilityMeasure rho]
    {digit : D → E} (hdigit : Measurable digit) (q : ℝ)
    (mu : Measure E) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (affineIndependentCopyLaw rho digit q mu) := by
  letI : IsProbabilityMeasure (rho.map digit) :=
    Measure.isProbabilityMeasure_map hdigit.aemeasurable
  letI : IsProbabilityMeasure (mu.map (q • ·)) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable (q • ·)).aemeasurable
  unfold affineIndependentCopyLaw
  infer_instance

/-- The convolution definition of `affineIndependentCopyLaw` is the direct
pushforward of the product law by `(d, x) ↦ digit d + q • x`. -/
theorem affineIndependentCopyLaw_eq_map_prod
    {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (rho : Measure D) (mu : Measure E) [SFinite rho] [SFinite mu]
    {digit : D → E} (hdigit : Measurable digit) (q : ℝ) :
    affineIndependentCopyLaw rho digit q mu =
      (rho.prod mu).map (fun p => digit p.1 + q • p.2) := by
  unfold affineIndependentCopyLaw Measure.conv
  rw [Measure.map_prod_map rho mu hdigit (by fun_prop),
    Measure.map_map (by fun_prop) (hdigit.prodMap (by fun_prop))]
  congr 1

/-- The characteristic function of an affine independent-copy law factors
into the characteristic function of the digit and the scaled copy. -/
theorem charFun_affineIndependentCopyLaw
    {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {rho : Measure D} [IsProbabilityMeasure rho]
    (digit : D → E) (q : ℝ)
    (mu : Measure E) [IsProbabilityMeasure mu] (t : E) :
    charFun (affineIndependentCopyLaw rho digit q mu) t =
      charFun (rho.map digit) t * charFun mu (q • t) := by
  letI : IsProbabilityMeasure (mu.map (q • ·)) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable (q • ·)).aemeasurable
  rw [affineIndependentCopyLaw, charFun_conv, charFun_map_smul]

/-- A fixed point of the affine independent-copy operator satisfies the
one-step characteristic-function recurrence. -/
theorem charFun_eq_mul_charFun_of_affineIndependentCopy_fixedPoint
    {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {rho : Measure D} [IsProbabilityMeasure rho]
    (digit : D → E) (q : ℝ)
    (mu : Measure E) [IsProbabilityMeasure mu]
    (hmu : Function.IsFixedPt (affineIndependentCopyLaw rho digit q) mu)
    (t : E) :
    charFun mu t = charFun (rho.map digit) t * charFun mu (q • t) := by
  calc
    charFun mu t = charFun (affineIndependentCopyLaw rho digit q mu) t :=
      congrArg (fun nu : Measure E => charFun nu t) hmu.symm
    _ = charFun (rho.map digit) t * charFun mu (q • t) :=
      charFun_affineIndependentCopyLaw digit q mu t

/-- Iterating the affine fixed-point recurrence separates the first `n`
digit factors from the residual characteristic function at `q ^ n • t`. -/
theorem charFun_iterate_of_affineIndependentCopy_fixedPoint
    {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {rho : Measure D} [IsProbabilityMeasure rho]
    (digit : D → E) (q : ℝ)
    (mu : Measure E) [IsProbabilityMeasure mu]
    (hmu : Function.IsFixedPt (affineIndependentCopyLaw rho digit q) mu)
    (n : ℕ) (t : E) :
    charFun mu t =
      (Finset.prod (Finset.range n)
        (fun k => charFun (rho.map digit) (q ^ k • t))) *
        charFun mu (q ^ n • t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have harg : q • (q ^ n • t) = q ^ (Nat.succ n) • t := by
        simp only [smul_smul, pow_succ]
        rw [mul_comm]
      rw [ih,
        charFun_eq_mul_charFun_of_affineIndependentCopy_fixedPoint
          digit q mu hmu (q ^ n • t),
        harg, Finset.prod_range_succ]
      ring

/-- Two probability measures are equal when their characteristic functions
satisfy the same contractive affine recurrence with a norm-at-most-one
multiplier. -/
theorem eq_of_charFun_affine_recurrence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    {mu nu : Measure E} [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] {q : ℝ} (hq : |q| < 1)
    (a : E → ℂ) (ha : ∀ t, ‖a t‖ ≤ 1)
    (hmu : ∀ t, charFun mu t = a t * charFun mu (q • t))
    (hnu : ∀ t, charFun nu t = a t * charFun nu (q • t)) :
    mu = nu := by
  apply Measure.ext_of_charFun
  funext t
  have hstep (s : E) :
      ‖charFun mu s - charFun nu s‖ ≤
        ‖charFun mu (q • s) - charFun nu (q • s)‖ := by
    rw [hmu s, hnu s, ← mul_sub, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ha s)
  have hiterate : ∀ n : ℕ,
      ‖charFun mu t - charFun nu t‖ ≤
        ‖charFun mu (q ^ n • t) - charFun nu (q ^ n • t)‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have harg : q • (q ^ n • t) = q ^ (Nat.succ n) • t := by
          simp only [smul_smul, pow_succ]
          rw [mul_comm]
        exact ih.trans (by simpa only [harg] using hstep (q ^ n • t))
  have hqt : Tendsto (fun n : ℕ => q ^ n • t) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).smul_const t
  have hmu_tendsto :
      Tendsto (fun n : ℕ => charFun mu (q ^ n • t)) atTop
        (𝓝 (charFun mu 0)) := by
    change Tendsto (charFun mu ∘ fun n : ℕ => q ^ n • t) atTop
      (𝓝 (charFun mu 0))
    exact ((continuous_charFun (μ := mu)).tendsto 0).comp hqt
  have hnu_tendsto :
      Tendsto (fun n : ℕ => charFun nu (q ^ n • t)) atTop
        (𝓝 (charFun nu 0)) := by
    change Tendsto (charFun nu ∘ fun n : ℕ => q ^ n • t) atTop
      (𝓝 (charFun nu 0))
    exact ((continuous_charFun (μ := nu)).tendsto 0).comp hqt
  have htail : Tendsto
      (fun n : ℕ => ‖charFun mu (q ^ n • t) - charFun nu (q ^ n • t)‖)
      atTop (𝓝 0) := by
    simpa [charFun_zero] using (hmu_tendsto.sub hnu_tendsto).norm
  have hle : ‖charFun mu t - charFun nu t‖ ≤ 0 :=
    ge_of_tendsto htail (Filter.Eventually.of_forall hiterate)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

/-- For `|q| < 1`, the affine independent-copy operator has at most one
probability fixed point. -/
theorem affineIndependentCopyLaw_fixedPoint_unique
    {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    {rho : Measure D} [IsProbabilityMeasure rho]
    {digit : D → E} (hdigit : Measurable digit)
    {q : ℝ} (hq : |q| < 1)
    {mu nu : Measure E} [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    (hmu : Function.IsFixedPt (affineIndependentCopyLaw rho digit q) mu)
    (hnu : Function.IsFixedPt (affineIndependentCopyLaw rho digit q) nu) :
    mu = nu := by
  letI : IsProbabilityMeasure (rho.map digit) :=
    Measure.isProbabilityMeasure_map hdigit.aemeasurable
  refine eq_of_charFun_affine_recurrence hq (charFun (rho.map digit))
    (fun t => norm_charFun_le_one t) ?_ ?_
  · exact fun t =>
      charFun_eq_mul_charFun_of_affineIndependentCopy_fixedPoint
        digit q mu hmu t
  · exact fun t =>
      charFun_eq_mul_charFun_of_affineIndependentCopy_fixedPoint
        digit q nu hnu t

/-- Product-map form of affine fixed-point uniqueness: a probability law
satisfying `X =_d digit D + q • X'`, with `D` and `X'` independent, is unique
when `|q| < 1`. -/
theorem affineIndependentCopy_map_fixedPoint_unique
    {D E : Type*} [MeasurableSpace D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    {rho : Measure D} [IsProbabilityMeasure rho]
    {digit : D → E} (hdigit : Measurable digit)
    {q : ℝ} (hq : |q| < 1)
    {mu nu : Measure E} [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    (hmu : mu = (rho.prod mu).map (fun p => digit p.1 + q • p.2))
    (hnu : nu = (rho.prod nu).map (fun p => digit p.1 + q • p.2)) :
    mu = nu := by
  apply affineIndependentCopyLaw_fixedPoint_unique
    (rho := rho) (digit := digit) (q := q) (mu := mu) (nu := nu)
    hdigit hq
  · exact (affineIndependentCopyLaw_eq_map_prod rho mu hdigit q).trans hmu.symm
  · exact (affineIndependentCopyLaw_eq_map_prod rho nu hdigit q).trans hnu.symm

end

end ProbabilityTheory
