import FabiusFunction.WeakConvergence
import FabiusFunction.EarlyMeasureBridge
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# From atomic approximants to step-function integrals

This module supplies the analytic bridge used in Theorem 2 of arXiv:1702.05442.  It identifies
the half-endpoint cells with ordinary interval indicators almost everywhere, computes their
integrals exactly, and sandwiches a histogram integral between slightly shrunken and enlarged
interval masses of `finiteConvolutionMeasure`.  Weak convergence and atomlessness of the limiting
density then give convergence of every interval integral.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal MeasureTheory Topology Interval
open Filter Finset MeasureTheory Set

namespace Fabius

noncomputable section

/-- The half-endpoint cell indicator agrees Lebesgue-almost everywhere with the
ordinary indicator of `Ioc a b`, the two endpoints forming a null set.  This is
what lets every integral of `halfEndpointIntervalIndicator` below be reduced to
Mathlib's `Ioc` indicator lemmas. -/
theorem halfEndpointIntervalIndicator_ae_eq_indicator (a b : ℝ) :
    halfEndpointIntervalIndicator a b =ᵐ[volume]
      (Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) := by
  filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume b] with x hxa hxb
  simp only [halfEndpointIntervalIndicator, hxa, hxb, false_or, if_false]
  by_cases h : a < x ∧ x < b
  · rw [if_pos h]
    simp [h.1, h.2.le]
  · rw [if_neg h]
    simp only [Set.indicator, Set.mem_Ioc]
    split_ifs with hx
    · exact (h ⟨hx.1, hx.2.lt_of_ne hxb⟩).elim
    · rfl

/-- The half-endpoint cell indicator is Lebesgue integrable on all of `ℝ`,
being almost everywhere the indicator of a bounded interval. -/
theorem halfEndpointIntervalIndicator_integrable (a b : ℝ) :
    Integrable (halfEndpointIntervalIndicator a b) := by
  rw [integrable_congr (halfEndpointIntervalIndicator_ae_eq_indicator a b)]
  exact (integrableOn_const (μ := volume) (s := Ioc a b) (C := (1 : ℝ))
    (measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc

/-- Interval-integrability of the half-endpoint cell indicator on an arbitrary
`c..d`, an immediate corollary of `halfEndpointIntervalIndicator_integrable`. -/
theorem halfEndpointIntervalIndicator_intervalIntegrable (a b c d : ℝ) :
    IntervalIntegrable (halfEndpointIntervalIndicator a b) volume c d :=
  (halfEndpointIntervalIndicator_integrable a b).intervalIntegrable

/-- The integral of the half-endpoint cell indicator over the whole line is
`max (b - a) 0`, the truncation recording that `Ioc a b` is empty when `b < a`.
This is the per-cell input to `integral_stepApproximant`. -/
theorem integral_halfEndpointIntervalIndicator (a b : ℝ) :
    (∫ x : ℝ, halfEndpointIntervalIndicator a b x) = max (b - a) 0 := by
  rw [integral_congr_ae (halfEndpointIntervalIndicator_ae_eq_indicator a b)]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ioc, Real.volume_real_Ioc]
  simp

/-- On an ordered interval `c ≤ d`, the integral of the half-endpoint cell
indicator is `max (min d b - max c a) 0`, the length of the overlap
`Ioc c d ∩ Ioc a b`. -/
theorem intervalIntegral_halfEndpointIntervalIndicator_of_le
    (a b c d : ℝ) (hcd : c ≤ d) :
    (∫ x in c..d, halfEndpointIntervalIndicator a b x) =
      max (min d b - max c a) 0 := by
  rw [intervalIntegral.integral_of_le hcd]
  rw [← integral_indicator measurableSet_Ioc]
  calc
    (∫ x : ℝ, (Ioc c d).indicator (halfEndpointIntervalIndicator a b) x) =
        ∫ x : ℝ, (Ioc c d ∩ Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)) x := by
      apply integral_congr_ae
      filter_upwards [halfEndpointIntervalIndicator_ae_eq_indicator a b] with x hx
      by_cases hxcd : x ∈ Ioc c d
      · simp only [Set.indicator_of_mem hxcd, hx]
        by_cases hxab : x ∈ Ioc a b
        · simp [hxcd, hxab]
        · simp [hxcd, hxab]
      · simp [hxcd]
    _ = volume.real (Ioc c d ∩ Ioc a b) := by
      rw [integral_indicator_const (1 : ℝ) (measurableSet_Ioc.inter measurableSet_Ioc)]
      simp
    _ = max (min d b - max c a) 0 := by
      rw [show Ioc c d ∩ Ioc a b = Ioc (max c a) (min d b) by
        ext x
        simp only [mem_inter_iff, Set.mem_Ioc, max_lt_iff, le_min_iff]
        tauto]
      exact Real.volume_real_Ioc

/-- For `c ≤ d`, the integral of the step approximant `φ_n` over `c..d` is the
prefactor `2 ^ n / 2 ^ (n + 1).choose 2` times the sum over `m` of the
coefficient `coeff m` weighted by the overlap length of `c..d` with the `m`-th
histogram cell.  This is the raw expansion later repackaged by
`intervalIntegral_stepApproximant_eq_mass_overlap`. -/
theorem intervalIntegral_stepApproximant_of_le (n : ℕ) (c d : ℝ) (hcd : c ≤ d) :
    (∫ x in c..d, stepApproximant n x) =
      (2 : ℝ) ^ n / (2 : ℝ) ^ ((n + 1).choose 2) *
        ∑ m ∈ range (approximationDegree n + 1),
          ((approximationPolynomial n).coeff m : ℝ) *
            max (min d (stepIntervalRight n m) - max c (stepIntervalLeft n m)) 0 := by
  unfold stepApproximant
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply congrArg ((2 : ℝ) ^ n / (2 : ℝ) ^ ((n + 1).choose 2) * ·)
    apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral_halfEndpointIntervalIndicator_of_le _ _ _ _ hcd]
  · intro m hm
    exact ((halfEndpointIntervalIndicator_intervalIntegrable
      (stepIntervalLeft n m) (stepIntervalRight n m) c d).const_mul _)

/-- Every finite histogram approximant is integrable on the real line. -/
theorem stepApproximant_integrable (n : ℕ) : Integrable (stepApproximant n) := by
  unfold stepApproximant
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro m hm
  exact (halfEndpointIntervalIndicator_integrable
    (stepIntervalLeft n m) (stepIntervalRight n m)).const_mul _

/-- Every finite histogram approximant is interval-integrable. -/
theorem stepApproximant_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (stepApproximant n) volume a b :=
  (stepApproximant_integrable n).intervalIntegrable

/-- The density measure `rvachevMeasure F` charges no singleton: it is given by
a density against Lebesgue measure, and points are Lebesgue null. -/
theorem rvachevMeasure_singleton (F : BoundedFabius) (x : ℝ) :
    rvachevMeasure F {x} = 0 := by
  exact withDensity_absolutelyContinuous volume _ (measure_singleton x)

/-- The frontier of `Ioc a b` is `rvachevMeasure F`-null.  This is the
null-boundary hypothesis required by the portmanteau theorem in
`finiteConvolutionMeasure_Ioc_tendsto`. -/
theorem rvachevMeasure_frontier_Ioc (F : BoundedFabius) (a b : ℝ) :
    rvachevMeasure F (frontier (Ioc a b)) = 0 := by
  by_cases hab : a < b
  · rw [frontier_Ioc hab]
    exact measure_union_null (rvachevMeasure_singleton F a)
      (rvachevMeasure_singleton F b)
  · rw [Ioc_eq_empty hab, frontier_empty]
    exact measure_empty

/-- Under `IsFabius F`, the mass of `Ioc a b` under the finite convolution
measures converges to its mass under `rvachevMeasure F`.  This is weak
convergence together with the null frontier of `Ioc a b`, read through
portmanteau. -/
theorem finiteConvolutionMeasure_Ioc_tendsto
    (F : BoundedFabius) (hF : IsFabius F) (a b : ℝ) :
    Tendsto (fun n : ℕ => (finiteConvolutionMeasure n).real (Ioc a b)) atTop
      (𝓝 ((rvachevMeasure F).real (Ioc a b))) := by
  letI : IsProbabilityMeasure (rvachevMeasure F) := rvachevMeasure_isProbability F hF
  have hENN := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (finiteConvolutionProbability_tendsto F hF)
    (rvachevMeasure_frontier_Ioc F a b)
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (rvachevMeasure F) (Ioc a b))).comp hENN
  simpa [finiteConvolutionProbability, rvachevProbability, Measure.real,
    Function.comp_def] using hreal

/-- Under `IsFabius F` and for `a ≤ b`, the mass of `Ioc a b` under the density
measure equals the interval integral of `rvachevUp F` over `a..b`.  This turns
the measure-theoretic limit into the analytic one wanted for Theorem 2. -/
theorem rvachevMeasure_real_Ioc_eq_intervalIntegral
    (F : BoundedFabius) (hF : IsFabius F) (a b : ℝ) (hab : a ≤ b) :
    (rvachevMeasure F).real (Ioc a b) = ∫ x in a..b, rvachevUp F x := by
  unfold rvachevMeasure
  rw [Measure.real, withDensity_apply _ measurableSet_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [ENNReal.toReal_ofReal]
    · exact intervalIntegral.integral_of_le hab |>.symm
    · exact setIntegral_nonneg measurableSet_Ioc fun x _ => rvachevUp_nonneg F x
  · exact (rvachevUp_integrable F hF).integrableOn
  · exact Eventually.of_forall (rvachevUp_nonneg F)

/-- The interval integral of `rvachevUp F` over `a..b` is nonnegative when
`a ≤ b`, since `rvachevUp F` is pointwise nonnegative. -/
theorem intervalIntegral_rvachevUp_nonneg
    (F : BoundedFabius) (a b : ℝ) (hab : a ≤ b) :
    0 ≤ ∫ x in a..b, rvachevUp F x :=
  intervalIntegral.integral_nonneg hab fun x _ => rvachevUp_nonneg F x

/-- Under `IsFabius F` and for `a ≤ b`, the interval integral of `rvachevUp F`
over `a..b` is at most the length `b - a`, since `rvachevUp F` is bounded by
one. -/
theorem intervalIntegral_rvachevUp_le_length
    (F : BoundedFabius) (hF : IsFabius F) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, rvachevUp F x) ≤ b - a := by
  calc
    (∫ x in a..b, rvachevUp F x) ≤ ∫ _ in a..b, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hab
        ((rvachevUp_integrable F hF).intervalIntegrable)
        (continuous_const.intervalIntegrable _ _)
      intro x _
      exact rvachevUp_le_one F x
    _ = b - a := by simp

/-- Under `IsFabius F`, with `a ≤ b` and `0 ≤ δ`, enlarging `a..b` by `δ` at each
end raises the integral of `rvachevUp F` by at most `2 * δ`.  This bounds the
outer side of the sandwich in `intervalIntegral_stepApproximant_tendsto_of_le`. -/
theorem intervalIntegral_rvachevUp_expand_sub_le
    (F : BoundedFabius) (hF : IsFabius F) (a b δ : ℝ)
    (_hab : a ≤ b) (hδ : 0 ≤ δ) :
    (∫ x in (a - δ)..(b + δ), rvachevUp F x) -
        (∫ x in a..b, rvachevUp F x) ≤ 2 * δ := by
  have hint (c d : ℝ) : IntervalIntegrable (rvachevUp F) volume c d :=
    (rvachevUp_integrable F hF).intervalIntegrable
  have hleft := intervalIntegral_rvachevUp_le_length F hF (a - δ) a (by linarith)
  have hright := intervalIntegral_rvachevUp_le_length F hF b (b + δ) (by linarith)
  have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
    (hint (a - δ) a) (hint a b)
  have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
    (hint (a - δ) b) (hint b (b + δ))
  linarith

/-- Under `IsFabius F`, with `0 ≤ δ` and the nondegeneracy hypothesis
`a + δ ≤ b - δ`, shrinking `a..b` by `δ` at each end lowers the integral of
`rvachevUp F` by at most `2 * δ`.  This bounds the inner side of the same
sandwich. -/
theorem intervalIntegral_rvachevUp_sub_shrink_le
    (F : BoundedFabius) (hF : IsFabius F) (a b δ : ℝ)
    (_hinner : a + δ ≤ b - δ) (hδ : 0 ≤ δ) :
    (∫ x in a..b, rvachevUp F x) -
        (∫ x in (a + δ)..(b - δ), rvachevUp F x) ≤ 2 * δ := by
  have hint (c d : ℝ) : IntervalIntegrable (rvachevUp F) volume c d :=
    (rvachevUp_integrable F hF).intervalIntegrable
  have hleft := intervalIntegral_rvachevUp_le_length F hF a (a + δ) (by linarith)
  have hright := intervalIntegral_rvachevUp_le_length F hF (b - δ) b (by linarith)
  have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
    (hint a (a + δ)) (hint (a + δ) (b - δ))
  have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
    (hint a (b - δ)) (hint (b - δ) b)
  linarith

/-- The mass that `polynomialMeasure n` gives to `Ioc a b` is the sum of the
normalized coefficients `coeff m / 2 ^ (n + 1).choose 2` over those atom
locations `polynomialAtomLocation n m` that lie in `Ioc a b`.  This is the
atom-counting side of the sandwich against the histogram integral. -/
theorem polynomialMeasure_real_Ioc (n : ℕ) (a b : ℝ) :
    (polynomialMeasure n).real (Ioc a b) =
      ∑ m ∈ range (approximationDegree n + 1),
        ((approximationPolynomial n).coeff m : ℝ) /
          (2 : ℝ) ^ ((n + 1).choose 2) *
            if polynomialAtomLocation n m ∈ Ioc a b then 1 else 0 := by
  unfold polynomialMeasure Measure.real
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Ioc, smul_eq_mul]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [ENNReal.toReal_mul, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    by_cases hloc : polynomialAtomLocation n m ∈ Ioc a b
    · simp [hloc]
    · simp [hloc]
  · intro _ _
    apply ENNReal.mul_ne_top
    · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)
    · simp only [Set.indicator]
      split_ifs <;> simp

/-- The `m`-th atom location lies strictly to the right of the left endpoint of
its histogram cell. -/
theorem stepIntervalLeft_lt_atom (n m : ℕ) :
    stepIntervalLeft n m < polynomialAtomLocation n m := by
  unfold stepIntervalLeft polynomialAtomLocation
  have hden : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  apply (div_lt_div_iff_of_pos_right hden).2
  linarith

/-- The `m`-th atom location lies strictly to the left of the right endpoint of
its histogram cell.  Together with `stepIntervalLeft_lt_atom` this places the
atom in the open cell, which is what makes `halfEndpointIntervalIndicator_atom`
evaluate to one. -/
theorem atom_lt_stepIntervalRight (n m : ℕ) :
    polynomialAtomLocation n m < stepIntervalRight n m := by
  unfold stepIntervalRight polynomialAtomLocation
  have hden : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  apply (div_lt_div_iff_of_pos_right hden).2
  linarith

@[simp] theorem halfEndpointIntervalIndicator_atom (n m : ℕ) :
    halfEndpointIntervalIndicator (stepIntervalLeft n m) (stepIntervalRight n m)
      (polynomialAtomLocation n m) = 1 := by
  rw [halfEndpointIntervalIndicator]
  split_ifs with hboundary hinterior
  · rcases hboundary with h | h
    · exact (stepIntervalLeft_lt_atom n m).ne h.symm |>.elim
    · exact (atom_lt_stepIntervalRight n m).ne h |>.elim
  · rfl
  · exact (hinterior ⟨stepIntervalLeft_lt_atom n m,
      atom_lt_stepIntervalRight n m⟩).elim

/-- Conditional height-to-mass estimate: if the step approximant `φ_n` is at
most one at the `m`-th atom, then the normalized atom mass
`coeff m / 2 ^ (n + 1).choose 2` is at most the cell width `1 / 2 ^ n`.  The
hypothesis is discharged globally in `StepApproximationLimit` by
`polynomialAtomMass_le_cellWidth_unconditional`. -/
theorem polynomialAtomMass_le_cellWidth (n m : ℕ)
    (hstep : stepApproximant n (polynomialAtomLocation n m) ≤ 1) :
    ((approximationPolynomial n).coeff m : ℝ) /
        (2 : ℝ) ^ ((n + 1).choose 2) ≤ 1 / (2 : ℝ) ^ n := by
  have hterm :
      ((approximationPolynomial n).coeff m : ℝ) ≤
        ∑ j ∈ range (approximationDegree n + 1),
          ((approximationPolynomial n).coeff j : ℝ) *
            halfEndpointIntervalIndicator (stepIntervalLeft n j)
              (stepIntervalRight n j) (polynomialAtomLocation n m) := by
    by_cases hm : m ∈ range (approximationDegree n + 1)
    · have hsingle := Finset.single_le_sum (s := range (approximationDegree n + 1))
        (f := fun j => ((approximationPolynomial n).coeff j : ℝ) *
          halfEndpointIntervalIndicator (stepIntervalLeft n j)
            (stepIntervalRight n j) (polynomialAtomLocation n m))
        (fun j hj => mul_nonneg (Nat.cast_nonneg _)
          (halfEndpointIntervalIndicator_nonneg _ _ _)) hm
      simpa using hsingle
    · have hmdegree : (approximationPolynomial n).natDegree < m := by
        rw [approximationPolynomial_natDegree]
        simpa using hm
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hmdegree]
      norm_num
      exact Finset.sum_nonneg fun j hj =>
        mul_nonneg (Nat.cast_nonneg ((approximationPolynomial n).coeff j))
          (halfEndpointIntervalIndicator_nonneg _ _ _)
  have hfactor : 0 ≤ (2 : ℝ) ^ n / (2 : ℝ) ^ ((n + 1).choose 2) := by positivity
  have hheight :
      (2 : ℝ) ^ n / (2 : ℝ) ^ ((n + 1).choose 2) *
          ((approximationPolynomial n).coeff m : ℝ) ≤ 1 := by
    refine (mul_le_mul_of_nonneg_left hterm hfactor).trans ?_
    simpa only [stepApproximant] using hstep
  apply (le_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ n by positivity)).2
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hheight

/-- Half the width of a level-`n` histogram cell, namely `1 / 2 ^ (n + 1)`.
Each cell is centred at its atom location and has full width `1 / 2 ^ n`, so
this is the amount by which an interval is shrunk or enlarged when it is
compared with the cells it meets. -/
noncomputable def stepHalfWidth (n : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (n + 1)

/-- The half-width `stepHalfWidth n` is strictly positive. -/
theorem stepHalfWidth_pos (n : ℕ) : 0 < stepHalfWidth n := by
  unfold stepHalfWidth
  positivity

/-- The half-widths tend to zero, so for every fixed `δ > 0` the level-`n`
comparison intervals eventually nest against the fixed ones: `Ioc (a + δ) (b - δ)`
sits inside the shrunken interval, and the enlarged interval sits inside
`Ioc (a - δ) (b + δ)`. -/
theorem tendsto_stepHalfWidth : Tendsto stepHalfWidth atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (show |(1 / 2 : ℝ)| < 1 by norm_num)).comp (tendsto_add_atTop_nat 1)
  exact h.congr' (Eventually.of_forall fun n => by
    simp [stepHalfWidth, one_div, inv_pow])

/-- The left endpoint of the `m`-th cell is its atom location minus the
half-width. -/
theorem stepIntervalLeft_eq_atom_sub (n m : ℕ) :
    stepIntervalLeft n m = polynomialAtomLocation n m - stepHalfWidth n := by
  unfold stepIntervalLeft polynomialAtomLocation stepHalfWidth
  ring

/-- The right endpoint of the `m`-th cell is its atom location plus the
half-width. -/
theorem stepIntervalRight_eq_atom_add (n m : ℕ) :
    stepIntervalRight n m = polynomialAtomLocation n m + stepHalfWidth n := by
  unfold stepIntervalRight polynomialAtomLocation stepHalfWidth
  ring

/-- Every level-`n` histogram cell has width `1 / 2 ^ n`, independently of the
cell index `m`. -/
theorem stepCellWidth_eq (n m : ℕ) :
    stepIntervalRight n m - stepIntervalLeft n m = 1 / (2 : ℝ) ^ n := by
  rw [stepIntervalRight_eq_atom_add, stepIntervalLeft_eq_atom_sub]
  unfold stepHalfWidth
  rw [pow_succ]
  ring

/-- The height factor `2 ^ n` and the cell width are reciprocal, so a cell of
the step approximant carries exactly the mass of its coefficient.  This is the
normalization used on both sides of the sandwich. -/
theorem stepCell_normalization (n m : ℕ) :
    (2 : ℝ) ^ n * (stepIntervalRight n m - stepIntervalLeft n m) = 1 := by
  rw [stepCellWidth_eq]
  field_simp

/-- Each histogram approximant has total mass one. -/
theorem integral_stepApproximant (n : ℕ) :
    (∫ x : ℝ, stepApproximant n x) = 1 := by
  unfold stepApproximant
  rw [integral_const_mul, integral_finsetSum]
  · have hwidth (m : ℕ) :
        max (stepIntervalRight n m - stepIntervalLeft n m) 0 =
          1 / (2 : ℝ) ^ n := by
      rw [stepCellWidth_eq, max_eq_left]
      positivity
    simp_rw [integral_const_mul, integral_halfEndpointIntervalIndicator,
      hwidth]
    rw [← Finset.sum_mul]
    have hcoeff :
        (∑ m ∈ range (approximationDegree n + 1),
            ((approximationPolynomial n).coeff m : ℝ)) =
          (2 : ℝ) ^ ((n + 1).choose 2) := by
      norm_cast
      exact sum_approximationPolynomial_coeff n
    rw [hcoeff]
    field_simp
  · intro m hm
    exact (halfEndpointIntervalIndicator_integrable
      (stepIntervalLeft n m) (stepIntervalRight n m)).const_mul _

/-- The nonnegative histogram approximants have exact `L¹` mass one. -/
theorem integral_abs_stepApproximant (n : ℕ) :
    (∫ x : ℝ, |stepApproximant n x|) = 1 := by
  calc
    (∫ x : ℝ, |stepApproximant n x|) =
        ∫ x : ℝ, stepApproximant n x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [abs_of_nonneg (stepApproximant_nonneg n x)]
    _ = 1 := integral_stepApproximant n

/-- Length of the overlap between the interval `a..b` and the `m`-th level-`n`
histogram cell, truncated at zero when the two are disjoint.  It is the shape in
which `intervalIntegral_stepApproximant_of_le` is compared with the atomic
masses of `polynomialMeasure n`. -/
noncomputable def stepOverlap (n m : ℕ) (a b : ℝ) : ℝ :=
  max (min b (stepIntervalRight n m) - max a (stepIntervalLeft n m)) 0

/-- Overlap lengths are nonnegative, by the truncation in the definition. -/
theorem stepOverlap_nonneg (n m : ℕ) (a b : ℝ) :
    0 ≤ stepOverlap n m a b := le_max_right _ _

/-- An overlap length never exceeds the width of the cell it is measured
against. -/
theorem stepOverlap_le_cellWidth (n m : ℕ) (a b : ℝ) :
    stepOverlap n m a b ≤ stepIntervalRight n m - stepIntervalLeft n m := by
  unfold stepOverlap
  have hw : 0 ≤ stepIntervalRight n m - stepIntervalLeft n m :=
    sub_nonneg.mpr (stepIntervalLeft_lt_right n m).le
  apply max_le
  · linarith [min_le_right b (stepIntervalRight n m),
      le_max_right a (stepIntervalLeft n m)]
  · exact hw

/-- Inner comparison: if the `m`-th atom lies in the shrunken interval
`Ioc (a + stepHalfWidth n) (b - stepHalfWidth n)`, then its whole cell lies in
`a..b`, so the atom indicator is at most the normalized overlap
`2 ^ n * stepOverlap n m a b`. -/
theorem innerAtomIndicator_le_normalizedOverlap (n m : ℕ) (a b : ℝ) :
    (if polynomialAtomLocation n m ∈
        Ioc (a + stepHalfWidth n) (b - stepHalfWidth n) then 1 else 0 : ℝ) ≤
      (2 : ℝ) ^ n * stepOverlap n m a b := by
  by_cases hz : polynomialAtomLocation n m ∈
      Ioc (a + stepHalfWidth n) (b - stepHalfWidth n)
  · rw [if_pos hz]
    have hl : a ≤ stepIntervalLeft n m := by
      rw [stepIntervalLeft_eq_atom_sub]
      linarith [hz.1]
    have hr : stepIntervalRight n m ≤ b := by
      rw [stepIntervalRight_eq_atom_add]
      linarith [hz.2]
    unfold stepOverlap
    rw [min_eq_right hr, max_eq_right hl,
      max_eq_left (sub_nonneg.mpr (stepIntervalLeft_lt_right n m).le),
      stepCell_normalization]
  · rw [if_neg hz]
    exact mul_nonneg (by positivity) (stepOverlap_nonneg n m a b)

/-- Outer comparison: the normalized overlap `2 ^ n * stepOverlap n m a b` is at
most the indicator of the `m`-th atom lying in the enlarged interval
`Ioc (a - stepHalfWidth n) (b + stepHalfWidth n)`, because an atom outside that
interval has a cell disjoint from `a..b`. -/
theorem normalizedOverlap_le_outerAtomIndicator (n m : ℕ) (a b : ℝ) :
    (2 : ℝ) ^ n * stepOverlap n m a b ≤
      (if polynomialAtomLocation n m ∈
        Ioc (a - stepHalfWidth n) (b + stepHalfWidth n) then 1 else 0 : ℝ) := by
  by_cases hz : polynomialAtomLocation n m ∈
      Ioc (a - stepHalfWidth n) (b + stepHalfWidth n)
  · rw [if_pos hz]
    calc
      (2 : ℝ) ^ n * stepOverlap n m a b ≤
          (2 : ℝ) ^ n *
            (stepIntervalRight n m - stepIntervalLeft n m) :=
        mul_le_mul_of_nonneg_left (stepOverlap_le_cellWidth n m a b) (by positivity)
      _ = 1 := stepCell_normalization n m
  · rw [if_neg hz]
    have hz' : polynomialAtomLocation n m ≤ a - stepHalfWidth n ∨
        b + stepHalfWidth n < polynomialAtomLocation n m := by
      simpa only [Set.mem_Ioc, not_and_or, not_lt, not_le] using hz
    have hoverlap : stepOverlap n m a b = 0 := by
      unfold stepOverlap
      apply max_eq_right
      rcases hz' with hzleft | hzright
      · have hr : stepIntervalRight n m ≤ a := by
          rw [stepIntervalRight_eq_atom_add]
          linarith
        linarith [min_le_right b (stepIntervalRight n m),
          le_max_left a (stepIntervalLeft n m)]
      · have hl : b < stepIntervalLeft n m := by
          rw [stepIntervalLeft_eq_atom_sub]
          linarith
        linarith [min_le_left b (stepIntervalRight n m),
          le_max_right a (stepIntervalLeft n m)]
    rw [hoverlap, mul_zero]

/-- For `a ≤ b`, the integral of `φ_n` over `a..b` is the sum over atoms of the
normalized coefficient times the normalized overlap `2 ^ n * stepOverlap`.
Matching this term by term with `polynomialMeasure_real_Ioc` yields both halves
of the sandwich. -/
theorem intervalIntegral_stepApproximant_eq_mass_overlap
    (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, stepApproximant n x) =
      ∑ m ∈ range (approximationDegree n + 1),
        (((approximationPolynomial n).coeff m : ℝ) /
          (2 : ℝ) ^ ((n + 1).choose 2)) *
            ((2 : ℝ) ^ n * stepOverlap n m a b) := by
  rw [intervalIntegral_stepApproximant_of_le n a b hab]
  unfold stepOverlap
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The histogram integral over `[a,b]` dominates the atomic mass whose cells lie
entirely inside that interval. -/
theorem polynomialMeasure_inner_le_intervalIntegral_stepApproximant
    (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    (polynomialMeasure n).real
        (Ioc (a + stepHalfWidth n) (b - stepHalfWidth n)) ≤
      ∫ x in a..b, stepApproximant n x := by
  rw [polynomialMeasure_real_Ioc,
    intervalIntegral_stepApproximant_eq_mass_overlap n a b hab]
  apply Finset.sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_left (innerAtomIndicator_le_normalizedOverlap n m a b)
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

/-- The histogram integral over `[a,b]` is dominated by the atomic mass whose
cells meet that interval. -/
theorem intervalIntegral_stepApproximant_le_polynomialMeasure_outer
    (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, stepApproximant n x) ≤
      (polynomialMeasure n).real
        (Ioc (a - stepHalfWidth n) (b + stepHalfWidth n)) := by
  rw [polynomialMeasure_real_Ioc,
    intervalIntegral_stepApproximant_eq_mass_overlap n a b hab]
  apply Finset.sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_left (normalizedOverlap_le_outerAtomIndicator n m a b)
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

/-- For `a ≤ b`, the mass the finite convolution measure gives to the shrunken
interval is at most the histogram integral over `a..b`.  This is the inner bound
transported along `polynomialMeasure_eq_finiteConvolutionMeasure`. -/
theorem finiteConvolutionMeasure_inner_le_intervalIntegral_stepApproximant
    (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    (finiteConvolutionMeasure n).real
        (Ioc (a + stepHalfWidth n) (b - stepHalfWidth n)) ≤
      ∫ x in a..b, stepApproximant n x := by
  rw [← polynomialMeasure_eq_finiteConvolutionMeasure n]
  exact polynomialMeasure_inner_le_intervalIntegral_stepApproximant n a b hab

/-- For `a ≤ b`, the histogram integral over `a..b` is at most the mass the
finite convolution measure gives to the enlarged interval.  This is the outer
bound transported along `polynomialMeasure_eq_finiteConvolutionMeasure`. -/
theorem intervalIntegral_stepApproximant_le_finiteConvolutionMeasure_outer
    (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, stepApproximant n x) ≤
      (finiteConvolutionMeasure n).real
        (Ioc (a - stepHalfWidth n) (b + stepHalfWidth n)) := by
  rw [← polynomialMeasure_eq_finiteConvolutionMeasure n]
  exact intervalIntegral_stepApproximant_le_polynomialMeasure_outer n a b hab

/-- The interval integrals of the histogram approximants converge to those of
Rvachev's up function.  This is the analytic bridge in Theorem 2. -/
theorem intervalIntegral_stepApproximant_tendsto_of_le
    (F : BoundedFabius) (hF : IsFabius F) (a b : ℝ) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => ∫ x in a..b, stepApproximant n x) atTop
      (𝓝 (∫ x in a..b, rvachevUp F x)) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := min (ε / 8) ((b - a) / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  have hδab : δ ≤ (b - a) / 4 := min_le_right _ _
  have hinner : a + δ ≤ b - δ := by linarith
  have houter : a - δ ≤ b + δ := by linarith
  have hgapInner := intervalIntegral_rvachevUp_sub_shrink_le
    F hF a b δ hinner hδ.le
  have hgapOuter := intervalIntegral_rvachevUp_expand_sub_le
    F hF a b δ hab.le hδ.le
  have hlimitInner := rvachevMeasure_real_Ioc_eq_intervalIntegral
    F hF (a + δ) (b - δ) hinner
  have hlimitOuter := rvachevMeasure_real_Ioc_eq_intervalIntegral
    F hF (a - δ) (b + δ) houter
  have htInner := finiteConvolutionMeasure_Ioc_tendsto
    F hF (a + δ) (b - δ)
  have htOuter := finiteConvolutionMeasure_Ioc_tendsto
    F hF (a - δ) (b + δ)
  rw [Metric.tendsto_atTop] at htInner htOuter
  obtain ⟨Ninner, hNinner⟩ := htInner (ε / 4) (by positivity)
  obtain ⟨Nouter, hNouter⟩ := htOuter (ε / 4) (by positivity)
  obtain ⟨Nwidth, hNwidth⟩ := eventually_atTop.mp
    (tendsto_stepHalfWidth.eventually_le_const hδ)
  refine ⟨max (max Ninner Nouter) Nwidth, fun n hn => ?_⟩
  have hninner : Ninner ≤ n := (le_max_left Ninner Nouter).trans
    ((le_max_left (max Ninner Nouter) Nwidth).trans hn)
  have hnouter : Nouter ≤ n := (le_max_right Ninner Nouter).trans
    ((le_max_left (max Ninner Nouter) Nwidth).trans hn)
  have hnwidth : Nwidth ≤ n := (le_max_right (max Ninner Nouter) Nwidth).trans hn
  have hw : stepHalfWidth n ≤ δ := hNwidth n hnwidth
  have hfixedInnerSubset :
      Ioc (a + δ) (b - δ) ⊆
        Ioc (a + stepHalfWidth n) (b - stepHalfWidth n) := by
    apply Set.Ioc_subset_Ioc <;> linarith
  have hmInner :
      (finiteConvolutionMeasure n).real (Ioc (a + δ) (b - δ)) ≤
        (finiteConvolutionMeasure n).real
          (Ioc (a + stepHalfWidth n) (b - stepHalfWidth n)) :=
    measureReal_mono hfixedInnerSubset
  have hlower :
      (finiteConvolutionMeasure n).real (Ioc (a + δ) (b - δ)) ≤
        ∫ x in a..b, stepApproximant n x :=
    hmInner.trans
      (finiteConvolutionMeasure_inner_le_intervalIntegral_stepApproximant n a b hab.le)
  have hmovingOuterSubset :
      Ioc (a - stepHalfWidth n) (b + stepHalfWidth n) ⊆
        Ioc (a - δ) (b + δ) := by
    apply Set.Ioc_subset_Ioc <;> linarith
  have hmOuter :
      (finiteConvolutionMeasure n).real
          (Ioc (a - stepHalfWidth n) (b + stepHalfWidth n)) ≤
        (finiteConvolutionMeasure n).real (Ioc (a - δ) (b + δ)) :=
    measureReal_mono hmovingOuterSubset
  have hupper :
      (∫ x in a..b, stepApproximant n x) ≤
        (finiteConvolutionMeasure n).real (Ioc (a - δ) (b + δ)) :=
    (intervalIntegral_stepApproximant_le_finiteConvolutionMeasure_outer
      n a b hab.le).trans hmOuter
  have hnearInner := hNinner n hninner
  have hnearOuter := hNouter n hnouter
  rw [hlimitInner, Real.dist_eq, abs_lt] at hnearInner
  rw [hlimitOuter, Real.dist_eq, abs_lt] at hnearOuter
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Endpoint-order-free interval-integral convergence. -/
theorem intervalIntegral_stepApproximant_tendsto
    (F : BoundedFabius) (hF : IsFabius F) (a b : ℝ) :
    Tendsto (fun n : ℕ => ∫ x in a..b, stepApproximant n x) atTop
      (𝓝 (∫ x in a..b, rvachevUp F x)) := by
  rcases le_total a b with hab | hba
  · exact intervalIntegral_stepApproximant_tendsto_of_le F hF a b hab
  · simpa only [intervalIntegral.integral_symm b a] using
      (intervalIntegral_stepApproximant_tendsto_of_le F hF b a hba).neg

end

end Fabius
