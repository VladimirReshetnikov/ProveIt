import FabiusFunction.DyadicClosedForm
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Polynomial and measure approximants from arXiv:1702.05442

This file formalizes equations (10)--(19), the bounded-partition interpretation following
equation (19), and the step functions used in Theorem 2 of the paper.

The polynomial API records the product and recursion formulas, exact degree,
coefficient interpretation, and coefficient normalization.  The measure API
then constructs the associated atomic probability measures and finite
Bernoulli convolutions, while the last section defines the corrected pointwise
step representatives and records their exact endpoint range, including the
base approximant at the origin.

Two corrections to the source are built into the definitions:

* The upper convolution index in equation (12) must be finite (`1 ≤ k ≤ n`), as required by
  equation (10) and by every subsequent use of `μ_n`.
* The interval indicators defining `φ_n` need boundary value `1/2`; ordinary indicators of
  closed intervals double-count adjacent endpoints and already give `φ_1(0) = 2`, contradicting
  the proof of Theorem 2.  The symmetric half-endpoint representative gives `φ_1(0) = 1`.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal MeasureTheory
open Finset MeasureTheory Set

namespace Fabius

open Polynomial

/-- `1 + X + ... + X^(r-1)`. -/
noncomputable def geometricPolynomial (r : ℕ) : Polynomial ℕ :=
  ∑ j : Fin r, X ^ j.val

/-- The geometric polynomial with no terms is zero. -/
@[simp] theorem geometricPolynomial_zero : geometricPolynomial 0 = 0 := by
  simp [geometricPolynomial]

/-- The one-term geometric polynomial is the constant polynomial `1`. -/
@[simp] theorem geometricPolynomial_one : geometricPolynomial 1 = 1 := by
  simp [geometricPolynomial]

/-- Splitting even and odd exponents gives the basic doubling identity for
geometric polynomials. -/
theorem geometricPolynomial_two_mul (r : ℕ) :
    geometricPolynomial (2 * r) =
      (geometricPolynomial r).comp (X ^ 2) * (1 + X) := by
  rw [geometricPolynomial, sum_fin_two_mul]
  simp only [geometricPolynomial]
  rw [Polynomial.sum_comp Finset.univ (fun j : Fin r => X ^ j.val) (X ^ 2),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [X_pow_comp]
  rw [pow_mul, pow_two]
  ring

/-- The polynomial `p_n` in equations (14), (15), and (19). -/
noncomputable def approximationPolynomial (n : ℕ) : Polynomial ℕ :=
  ∏ k ∈ range n, geometricPolynomial (2 ^ (k + 1))

/-- The zeroth approximation polynomial is the multiplicative identity. -/
@[simp] theorem approximationPolynomial_zero : approximationPolynomial 0 = 1 := by
  simp [approximationPolynomial]

/-- Appending the last geometric factor gives the direct product recurrence
for `p_n`. -/
theorem approximationPolynomial_succ_product (n : ℕ) :
    approximationPolynomial (n + 1) =
      approximationPolynomial n * geometricPolynomial (2 ^ (n + 1)) := by
  simp [approximationPolynomial, prod_range_succ]

/-- Equation (14). -/
theorem approximationPolynomial_succ (n : ℕ) :
    approximationPolynomial (n + 1) =
      (approximationPolynomial n).comp (X ^ 2) * (1 + X) ^ (n + 1) := by
  induction n with
  | zero => simp [approximationPolynomial, geometricPolynomial]
  | succ n ih =>
      calc
        approximationPolynomial (n + 1 + 1) =
            approximationPolynomial (n + 1) *
              geometricPolynomial (2 ^ (n + 1 + 1)) :=
          approximationPolynomial_succ_product (n + 1)
        _ = ((approximationPolynomial n).comp (X ^ 2) *
              (1 + X) ^ (n + 1)) *
              geometricPolynomial (2 ^ (n + 1 + 1)) := by rw [ih]
        _ = (approximationPolynomial (n + 1)).comp (X ^ 2) *
              (1 + X) ^ (n + 1 + 1) := by
          rw [show 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) by ring,
            geometricPolynomial_two_mul,
            approximationPolynomial_succ_product, mul_comp, pow_succ]
          ring

/-- The degree `g_n` of `p_n`. -/
def approximationDegree (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (2 ^ (k + 1) - 1)

/-- The zeroth approximation polynomial has degree parameter zero. -/
@[simp] theorem approximationDegree_zero : approximationDegree 0 = 0 := by
  simp [approximationDegree]

/-- Appending the last geometric factor increases the degree by
`2^(n+1) - 1`. -/
theorem approximationDegree_succ_add (n : ℕ) :
    approximationDegree (n + 1) =
      approximationDegree n + (2 ^ (n + 1) - 1) := by
  simp [approximationDegree, sum_range_succ]

/-- A subtraction-free closed form for `g_n`, convenient for natural-number
arithmetic. -/
theorem approximationDegree_eq (n : ℕ) :
    approximationDegree n + n + 2 = 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num [approximationDegree]
  | succ n ih =>
      rw [approximationDegree_succ_add, pow_succ]
      omega

/-- Closed form for the degree `g_n`, expressed with truncated natural
subtraction. -/
theorem approximationDegree_eq_sub (n : ℕ) :
    approximationDegree n = 2 ^ (n + 1) - n - 2 := by
  have hdegree := approximationDegree_eq n
  omega

/-- Equation (16). -/
theorem approximationDegree_succ (n : ℕ) :
    approximationDegree (n + 1) = 2 * approximationDegree n + (n + 1) := by
  rw [approximationDegree_succ_add]
  have h := approximationDegree_eq n
  omega

/-- Equation (17), with the displayed sum indexed from zero. -/
theorem approximationDegree_div_pow (n : ℕ) :
    (approximationDegree n : ℚ) / (2 : ℚ) ^ n =
      ∑ k ∈ range n, ((k + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [approximationDegree_succ, sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        pow_succ] at ih ⊢
      rw [← ih]
      ring

/-- Every coefficient below `r` in `1 + X + ⋯ + X^(r-1)` is one, and every
later coefficient is zero. -/
theorem geometricPolynomial_coeff (r m : ℕ) :
    (geometricPolynomial r).coeff m = if m < r then 1 else 0 := by
  unfold geometricPolynomial
  rw [Polynomial.finsetSum_coeff Finset.univ (fun j : Fin r => X ^ j.val) m]
  simp only [coeff_X_pow]
  by_cases h : m < r
  · rw [if_pos h, Fintype.sum_eq_single ⟨m, h⟩]
    · rw [if_pos (by rfl)]
    · intro b hne
      rw [if_neg]
      intro heq
      apply hne
      apply Fin.ext
      exact heq.symm
  · rw [if_neg h]
    apply Fintype.sum_eq_zero
    intro b
    rw [if_neg]
    intro heq
    apply h
    rw [heq]
    exact b.isLt

/-- A nonempty geometric polynomial has degree `r - 1`. -/
theorem geometricPolynomial_natDegree {r : ℕ} (hr : 0 < r) :
    (geometricPolynomial r).natDegree = r - 1 := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [geometricPolynomial_coeff, if_neg]
    omega
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [geometricPolynomial_coeff, if_pos (by omega)]
    norm_num

/-- Every nonempty geometric polynomial is monic. -/
theorem geometricPolynomial_monic {r : ℕ} (hr : 0 < r) :
    (geometricPolynomial r).Monic := by
  rw [Polynomial.Monic.def, ← Polynomial.coeff_natDegree,
    geometricPolynomial_natDegree hr, geometricPolynomial_coeff,
    if_pos (by omega)]

/-- Every polynomial approximant is monic. -/
theorem approximationPolynomial_monic (n : ℕ) :
    (approximationPolynomial n).Monic := by
  unfold approximationPolynomial
  apply Polynomial.monic_prod_of_monic
  intro k _hk
  exact geometricPolynomial_monic (by positivity)

/-- Restatement of `approximationPolynomial_monic` as a `simp` lemma: the
leading coefficient of `p_n` is `1`.  Monicity comes from the geometric
factors `1 + X + ⋯ + X^(2^(k+1) - 1)`, each of which is monic. -/
@[simp]
theorem approximationPolynomial_leadingCoeff (n : ℕ) :
    (approximationPolynomial n).leadingCoeff = 1 :=
  (approximationPolynomial_monic n).leadingCoeff

/-- The natural degree of `p_n` is exactly `g_n`. -/
theorem approximationPolynomial_natDegree (n : ℕ) :
    (approximationPolynomial n).natDegree = approximationDegree n := by
  unfold approximationPolynomial approximationDegree
  rw [Polynomial.natDegree_prod_of_monic]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [geometricPolynomial_natDegree]
    positivity
  · intro k hk
    exact geometricPolynomial_monic (by positivity)

/-- Coefficients strictly above the exact degree of `p_n` vanish. -/
theorem approximationPolynomial_coeff_eq_zero_of_degree_lt
    {n m : ℕ} (hm : approximationDegree n < m) :
    (approximationPolynomial n).coeff m = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rwa [approximationPolynomial_natDegree]

/-- Evaluating a geometric polynomial at one counts its `r` terms. -/
theorem geometricPolynomial_eval_one (r : ℕ) :
    (geometricPolynomial r).eval 1 = r := by
  unfold geometricPolynomial
  rw [Polynomial.eval_finsetSum Finset.univ (fun j : Fin r => X ^ j.val) 1]
  simp

/-- Evaluation at one gives the normalization constant for `p_n`. -/
theorem approximationPolynomial_eval_one (n : ℕ) :
    (approximationPolynomial n).eval 1 = 2 ^ (n + 1).choose 2 := by
  unfold approximationPolynomial
  rw [eval_prod]
  simp only [geometricPolynomial_eval_one]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [prod_range_succ, ih]
      have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega, show 2 = 1 + 1 by omega,
          Nat.choose_succ_succ]
        simp [Nat.choose_one_right]
        omega
      rw [hchoose, pow_add]
      ring_nf

/-- The coefficients of `p_n` have total mass `2^choose(n+1,2)`.  This is the
normalization used by both the polynomial probability measure and the step
approximant. -/
theorem sum_approximationPolynomial_coeff (n : ℕ) :
    ∑ m ∈ range (approximationDegree n + 1),
        (approximationPolynomial n).coeff m = 2 ^ (n + 1).choose 2 := by
  rw [← approximationPolynomial_eval_one]
  rw [Polynomial.eval_eq_sum_range]
  rw [approximationPolynomial_natDegree]
  simp

/-- A bounded `n`-part partition as in the combinatorial assertion after equation (19). -/
abbrev RestrictedPartition (n : ℕ) :=
  ∀ k : Fin n, Fin (2 ^ (k.val + 1))

/-- Sum of the parts of a bounded partition. -/
def restrictedPartitionWeight {n : ℕ} (s : RestrictedPartition n) : ℕ :=
  ∑ k, (s k).val

/-- Generating polynomial for the bounded partitions used in the paper. -/
noncomputable def restrictedPartitionPolynomial (n : ℕ) : Polynomial ℕ :=
  ∑ s : RestrictedPartition n, X ^ restrictedPartitionWeight s

/-- Expanding the product of geometric factors identifies `p_n` with the
generating polynomial of the bounded partitions: choosing one exponent from
each factor `1 + X + ⋯ + X^(2^(k+1) - 1)` is exactly choosing a
`RestrictedPartition n`, and the chosen exponents add.  This is the input
to `approximationPolynomial_coeff_eq_card`, which turns it into the
combinatorial assertion following equation (19). -/
theorem approximationPolynomial_eq_partitionPolynomial (n : ℕ) :
    approximationPolynomial n = restrictedPartitionPolynomial n := by
  unfold approximationPolynomial restrictedPartitionPolynomial
  rw [Finset.prod_range]
  simp_rw [geometricPolynomial]
  rw [Fintype.prod_sum]
  congr 1
  funext s
  simp [restrictedPartitionWeight, Finset.prod_pow_eq_pow_sum]

/-- Coefficients of `p_n` count the bounded partitions asserted after equation (19). -/
theorem approximationPolynomial_coeff_eq_card (n r : ℕ) :
    (approximationPolynomial n).coeff r =
      Fintype.card {s : RestrictedPartition n // restrictedPartitionWeight s = r} := by
  rw [approximationPolynomial_eq_partitionPolynomial]
  unfold restrictedPartitionPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_boole]
  rw [Fintype.card_subtype]
  simp [eq_comm]

/-- Location of the atom replacing `X^m` in the polynomial description following
equation (17). -/
noncomputable def polynomialAtomLocation (n m : ℕ) : ℝ :=
  ((2 : ℝ) * m - approximationDegree n) / (2 : ℝ) ^ (n + 1)

/-- The finite atomic measure obtained from
`2^(-choose (n+1) 2) * p_n` by replacing each monomial with its Dirac mass. -/
noncomputable def polynomialMeasure (n : ℕ) : Measure ℝ :=
  ∑ m ∈ range (approximationDegree n + 1),
    (((approximationPolynomial n).coeff m : ℝ≥0∞) /
      (2 : ℝ≥0∞) ^ ((n + 1).choose 2)) • Measure.dirac (polynomialAtomLocation n m)

/-- `polynomialMeasure n` is a probability measure: by
`sum_approximationPolynomial_coeff` the coefficients of `p_n` sum to
`2 ^ (n + 1).choose 2`, which is exactly the factor divided out in the
definition.  Together with the corresponding instance for
`finiteConvolutionMeasure` this supplies the hypotheses of
`Measure.ext_of_charFun` used in `EarlyMeasureBridge`. -/
instance polynomialMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (polynomialMeasure n) := by
  rw [isProbabilityMeasure_iff]
  simp only [polynomialMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, Measure.dirac_apply', MeasurableSet.univ,
    Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hcoeff :
      ∑ m ∈ range (approximationDegree n + 1),
          ((approximationPolynomial n).coeff m : ℝ≥0∞) =
        (2 : ℝ≥0∞) ^ ((n + 1).choose 2) := by
    norm_cast
    exact sum_approximationPolynomial_coeff n
  rw [hcoeff]
  exact ENNReal.mul_inv_cancel (by norm_num) (by simp)

/-- Expanding the finite atomic measure gives its characteristic function as a
normalized coefficient sum. -/
theorem polynomialMeasure_charFun_sum (n : ℕ) (t : ℝ) :
    charFun (polynomialMeasure n) t =
      ∑ m ∈ range (approximationDegree n + 1),
        (((approximationPolynomial n).coeff m : ℝ) /
          (2 : ℝ) ^ ((n + 1).choose 2)) *
          Complex.exp (t * polynomialAtomLocation n m * Complex.I) := by
  unfold charFun polynomialMeasure
  rw [integral_finsetSum_measure]
  · simp [integral_smul_measure, polynomialAtomLocation]
  · intro m hm
    exact (integrable_dirac (by simp)).smul_measure (by finiteness)

/-- A symmetric Bernoulli atom at scale `2^(-k-1)`. -/
noncomputable def centeredBernoulliMeasure (k : ℕ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac ((2 : ℝ) ^ (-(k + 1 : ℤ))) +
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-((2 : ℝ) ^ (-(k + 1 : ℤ))))

/-- `centeredBernoulliMeasure k` is a probability measure: its two atoms at
`±2^(-(k+1))` carry mass `1/2` each.  This is what lets the convolutions
built from it inherit `IsProbabilityMeasure`. -/
instance centeredBernoulliMeasure_isProbability (k : ℕ) :
    IsProbabilityMeasure (centeredBernoulliMeasure k) := by
  rw [isProbabilityMeasure_iff]
  simp [centeredBernoulliMeasure]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Repeated additive convolution, with the Dirac mass at zero as unit. -/
noncomputable def convolutionPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => μ ∗ convolutionPow μ n

/-- Convolution powers of a probability measure are again probability
measures, the exponent `0` case being the Dirac unit at zero.  Needed so
that `charFun_conv` applies in `convolutionPow_charFun`. -/
instance convolutionPow_isProbability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (convolutionPow μ n) := by
  induction n with
  | zero =>
      rw [isProbabilityMeasure_iff]
      simp [convolutionPow]
  | succ n ih =>
      rw [convolutionPow]
      infer_instance

/-- The corrected finite convolution from equation (12): the upper index is `n`, not infinity. -/
noncomputable def finiteConvolutionMeasure : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => finiteConvolutionMeasure n ∗
      convolutionPow (centeredBernoulliMeasure (n + 1)) (n + 1)

/-- The corrected finite convolution `μ_n` of equation (12) is a
probability measure, by induction over its finitely many Bernoulli
factors.  This is the instance behind `finiteConvolutionProbability` in
`WeakConvergence` and behind the `Measure.ext_of_charFun` step in
`EarlyMeasureBridge`. -/
instance finiteConvolutionMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (finiteConvolutionMeasure n) := by
  induction n with
  | zero =>
      rw [isProbabilityMeasure_iff]
      simp [finiteConvolutionMeasure]
  | succ n ih =>
      rw [finiteConvolutionMeasure]
      infer_instance

set_option maxHeartbeats 100000 in
/-- The characteristic function of the symmetric two-atom measure at
`±2^(-(k+1))` is `cos (t / 2^(k+1))`.  This is the single-factor
computation that `finiteConvolutionMeasure_charFun` raises to powers to
produce the finite cosine product of equation (12). -/
theorem centeredBernoulliMeasure_charFun (k : ℕ) (t : ℝ) :
    charFun (centeredBernoulliMeasure k) t =
      Real.cos (t / (2 : ℝ) ^ (k + 1)) := by
  let a : ℝ := (2 : ℝ) ^ (-(k + 1 : ℤ))
  let f : ℝ → ℂ := fun x => Complex.exp ((inner ℝ x t : ℝ) * Complex.I)
  have hpos : Integrable f ((2 : ℝ≥0∞)⁻¹ • Measure.dirac a) :=
    (integrable_dirac (by simp [f])).smul_measure (by simp)
  have hneg : Integrable f ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (-a)) :=
    (integrable_dirac (by simp [f])).smul_measure (by simp)
  unfold charFun centeredBernoulliMeasure
  change (∫ x, f x ∂((2 : ℝ≥0∞)⁻¹ • Measure.dirac a +
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-a))) = _
  rw [integral_add_measure hpos hneg]
  simp only [integral_smul_measure, integral_dirac]
  have hhalf : ((2 : ℝ≥0∞)⁻¹).toReal = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  simp only [f, Real.inner_apply, one_div, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_ofNat]
  have ha : a * t = t / (2 : ℝ) ^ (k + 1) := by
    dsimp [a]
    rw [zpow_neg,
      show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega,
      zpow_natCast]
    ring
  have hna : -a * t = -(t / (2 : ℝ) ^ (k + 1)) := by rw [← ha]; ring
  rw [ha, hna, Complex.ofReal_cos]
  rw [Complex.cos]
  push_cast
  ring

/-- Characteristic functions turn a finite convolution power into an ordinary
power. -/
theorem convolutionPow_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (t : ℝ) :
    charFun (convolutionPow μ n) t = (charFun μ t) ^ n := by
  induction n with
  | zero => simp [convolutionPow, charFun]
  | succ n ih =>
      rw [convolutionPow, charFun_conv, ih, pow_succ]
      ring

/-- The characteristic function of the corrected finite convolution in equation (12). -/
theorem finiteConvolutionMeasure_charFun (n : ℕ) (t : ℝ) :
    charFun (finiteConvolutionMeasure n) t =
      ∏ k ∈ range n,
        (Real.cos (t / (2 : ℝ) ^ (k + 2)) : ℂ) ^ (k + 1) := by
  induction n with
  | zero => simp [finiteConvolutionMeasure, charFun]
  | succ n ih =>
      rw [finiteConvolutionMeasure, charFun_conv,
        convolutionPow_charFun, centeredBernoulliMeasure_charFun, ih]
      simp [prod_range_succ]

/-- Indicator of `[a,b]` with boundary values `1/2`.  This is the pointwise
representative required in Theorem 2: using ordinary closed-interval indicators
would double-count adjacent endpoints (already giving value `2` at zero for `n = 1`). -/
noncomputable def halfEndpointIntervalIndicator (a b x : ℝ) : ℝ :=
  if x = a ∨ x = b then 1 / 2 else if a < x ∧ x < b then 1 else 0

/-- The left endpoint of the interval replacing the monomial `X^m` in Theorem 2. -/
noncomputable def stepIntervalLeft (n m : ℕ) : ℝ :=
  ((2 : ℝ) * m - 1 - approximationDegree n) / (2 : ℝ) ^ (n + 1)

/-- The right endpoint of the interval replacing the monomial `X^m` in Theorem 2. -/
noncomputable def stepIntervalRight (n m : ℕ) : ℝ :=
  ((2 : ℝ) * m + 1 - approximationDegree n) / (2 : ℝ) ^ (n + 1)

/-- The step function `φ_n` of Theorem 2, with the endpoint convention that makes
the paper's asserted identity `φ_n(0) = 1` literally true. -/
noncomputable def stepApproximant (n : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ n / (2 : ℝ) ^ ((n + 1).choose 2) *
    ∑ m ∈ range (approximationDegree n + 1),
      ((approximationPolynomial n).coeff m : ℝ) *
        halfEndpointIntervalIndicator (stepIntervalLeft n m) (stepIntervalRight n m) x

/-- Each interval used by the step approximant has strictly ordered endpoints. -/
theorem stepIntervalLeft_lt_right (n m : ℕ) :
    stepIntervalLeft n m < stepIntervalRight n m := by
  unfold stepIntervalLeft stepIntervalRight
  have hden : (0 : ℝ) < 2 ^ (n + 1) := pow_pos (by norm_num) _
  apply (div_lt_div_iff₀ hden hden).2
  linarith

/-- The half-endpoint indicator takes the value `1/2` at its left endpoint. -/
@[simp] theorem halfEndpointIntervalIndicator_self_left {a b : ℝ} :
    halfEndpointIntervalIndicator a b a = 1 / 2 := by
  simp [halfEndpointIntervalIndicator]

/-- The half-endpoint indicator takes the value `1/2` at its right endpoint. -/
@[simp] theorem halfEndpointIntervalIndicator_self_right {a b : ℝ} :
    halfEndpointIntervalIndicator a b b = 1 / 2 := by
  simp [halfEndpointIntervalIndicator]

/-- The half-endpoint representative always lies in `[0, 1]`, without any
ordering assumption on its displayed endpoints. -/
theorem halfEndpointIntervalIndicator_mem_Icc (a b x : ℝ) :
    halfEndpointIntervalIndicator a b x ∈ Icc (0 : ℝ) 1 := by
  unfold halfEndpointIntervalIndicator
  split_ifs <;> norm_num

/-- The half-endpoint interval representative is everywhere nonnegative. -/
theorem halfEndpointIntervalIndicator_nonneg (a b x : ℝ) :
    0 ≤ halfEndpointIntervalIndicator a b x :=
  (halfEndpointIntervalIndicator_mem_Icc a b x).1

/-- The zeroth step approximant is the half-endpoint indicator of `[-1/2, 1/2]`. -/
@[simp] theorem stepApproximant_zero (x : ℝ) :
    stepApproximant 0 x = halfEndpointIntervalIndicator (-1 / 2) (1 / 2) x := by
  simp [stepApproximant, stepIntervalLeft, stepIntervalRight, approximationDegree,
    approximationPolynomial]

/-- The base step approximant is exactly one at the origin. -/
theorem stepApproximant_zero_zero : stepApproximant 0 0 = 1 := by
  rw [stepApproximant_zero]
  norm_num [halfEndpointIntervalIndicator]

/-- The first step approximant takes the value one at the origin. -/
@[simp] theorem stepApproximant_one_zero : stepApproximant 1 0 = 1 := by
  have hp : approximationPolynomial 1 = 1 + X := by
    rw [show 1 = 0 + 1 by omega, approximationPolynomial_succ]
    simp
  rw [stepApproximant]
  norm_num [approximationDegree, hp, stepIntervalLeft, stepIntervalRight,
    halfEndpointIntervalIndicator, Finset.sum_range_succ]
  norm_num [Polynomial.coeff_one]

/-- Every corrected step approximant is pointwise nonnegative. -/
theorem stepApproximant_nonneg (n : ℕ) (x : ℝ) : 0 ≤ stepApproximant n x := by
  unfold stepApproximant
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (Nat.cast_nonneg _) (halfEndpointIntervalIndicator_nonneg _ _ _)

/-! ## The exact histogram-cell tiling

The gap register's *Exact histogram-cell tiling* candidate: the step
cells `I_{n,m} = [stepIntervalLeft n m, stepIntervalRight n m]` are
consecutive abutting intervals of common width `2^{-n}` whose union is
the single closed interval `[-1 + (n+1)/2^{n+1}, 1 - (n+1)/2^{n+1}]`,
consecutive cells meeting only at their shared endpoint.  The register
also asks for positivity of every in-range coefficient of the
approximation polynomial, upgrading the step approximant's support
enclosure to an exact description. -/

/-- Consecutive step cells abut: the right endpoint of cell `m` is the
left endpoint of cell `m + 1`. -/
theorem stepIntervalRight_eq_left_succ (n m : ℕ) :
    stepIntervalRight n m = stepIntervalLeft n (m + 1) := by
  unfold stepIntervalLeft stepIntervalRight
  push_cast
  ring

/-- The right endpoints increase with the cell index. -/
theorem stepIntervalRight_le_right {n : ℕ} {m m' : ℕ} (h : m ≤ m') :
    stepIntervalRight n m ≤ stepIntervalRight n m' := by
  unfold stepIntervalRight
  have hmm : (m : ℝ) ≤ (m' : ℝ) := Nat.cast_le.mpr h
  gcongr

/-- **Consecutive cells meet only at their common endpoint** (the
adjacency half of the register's tiling candidate). -/
theorem stepInterval_inter_succ (n m : ℕ) :
    Icc (stepIntervalLeft n m) (stepIntervalRight n m) ∩
      Icc (stepIntervalLeft n (m + 1)) (stepIntervalRight n (m + 1)) =
      {stepIntervalRight n m} := by
  have hshare := stepIntervalRight_eq_left_succ n m
  have h1 := stepIntervalLeft_lt_right n m
  have h2 := stepIntervalLeft_lt_right n (m + 1)
  have hRR : stepIntervalRight n m ≤ stepIntervalRight n (m + 1) := by
    rw [hshare]
    exact h2.le
  rw [Set.Icc_inter_Icc, ← hshare, max_eq_right h1.le, min_eq_left hRR,
    Set.Icc_self]

/-- **Finite interval coverage**: for any top index, the abutting step
cells tile a single closed interval. -/
theorem stepInterval_biUnion (n g : ℕ) :
    (⋃ m ∈ Finset.range (g + 1),
      Icc (stepIntervalLeft n m) (stepIntervalRight n m)) =
      Icc (stepIntervalLeft n 0) (stepIntervalRight n g) := by
  induction g with
  | zero => simp
  | succ g ih =>
      rw [Finset.range_add_one, Finset.set_biUnion_insert, ih, Set.union_comm,
        show stepIntervalLeft n (g + 1) = stepIntervalRight n g from
          (stepIntervalRight_eq_left_succ n g).symm,
        Set.Icc_union_Icc_eq_Icc]
      · exact (stepIntervalLeft_lt_right n 0).le.trans
          (stepIntervalRight_le_right (Nat.zero_le g))
      · rw [stepIntervalRight_eq_left_succ n g]
        exact (stepIntervalLeft_lt_right n (g + 1)).le

/-- The left endpoint of the first cell, evaluated. -/
theorem stepIntervalLeft_zero_eq (n : ℕ) :
    stepIntervalLeft n 0 = -1 + (n + 1) / (2 : ℝ) ^ (n + 1) := by
  unfold stepIntervalLeft
  have hcast : (approximationDegree n : ℝ) = 2 ^ (n + 1) - (n : ℝ) - 2 := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (approximationDegree_eq n)
    push_cast at h
    linarith
  have hpow : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  rw [hcast]
  field_simp
  ring

/-- The right endpoint of the last cell, evaluated. -/
theorem stepIntervalRight_degree_eq (n : ℕ) :
    stepIntervalRight n (approximationDegree n) =
      1 - (n + 1) / (2 : ℝ) ^ (n + 1) := by
  unfold stepIntervalRight
  have hcast : (approximationDegree n : ℝ) = 2 ^ (n + 1) - (n : ℝ) - 2 := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (approximationDegree_eq n)
    push_cast at h
    linarith
  have hpow : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  rw [hcast]
  field_simp
  ring

/-- **The exact histogram-cell tiling** (the register's candidate,
packaged): the `g_n + 1` step cells tile
`[-1 + (n+1)/2^{n+1}, 1 - (n+1)/2^{n+1}]` exactly. -/
theorem stepInterval_tiling (n : ℕ) :
    (⋃ m ∈ Finset.range (approximationDegree n + 1),
      Icc (stepIntervalLeft n m) (stepIntervalRight n m)) =
      Icc (-1 + (n + 1) / (2 : ℝ) ^ (n + 1))
        (1 - (n + 1) / (2 : ℝ) ^ (n + 1)) := by
  rw [stepInterval_biUnion, stepIntervalLeft_zero_eq,
    stepIntervalRight_degree_eq]

/-- **Every in-range coefficient of the approximation polynomial is
positive**: the polynomial is a product of all-ones geometric factors,
so each coefficient up to the degree receives at least one contributing
monomial.  This upgrades the step approximant's support enclosure to an
exact support description, as the register's tiling obligation asks. -/
theorem approximationPolynomial_coeff_pos (n : ℕ) :
    ∀ {m : ℕ}, m ≤ approximationDegree n →
      0 < (approximationPolynomial n).coeff m := by
  induction n with
  | zero =>
      intro m hm
      have hm0 : m = 0 := by
        simpa [approximationDegree] using hm
      simp [hm0]
  | succ n ih =>
      intro m hm
      rw [approximationPolynomial_succ_product, Polynomial.coeff_mul]
      have hD := approximationDegree_succ_add n
      set i₀ : ℕ := min m (approximationDegree n) with hi₀
      have hi₀le : i₀ ≤ approximationDegree n := min_le_right _ _
      have hi₀m : i₀ ≤ m := min_le_left _ _
      have hj₀ : m - i₀ < 2 ^ (n + 1) := by
        rcases le_or_gt m (approximationDegree n) with h | h
        · rw [hi₀, min_eq_left h]
          have hpow : 0 < 2 ^ (n + 1) := Nat.two_pow_pos (n + 1)
          omega
        · rw [hi₀, min_eq_right h.le]
          have hpow : 0 < 2 ^ (n + 1) := Nat.two_pow_pos (n + 1)
          omega
      refine Finset.sum_pos' (fun p _ => Nat.zero_le _) ⟨(i₀, m - i₀), ?_, ?_⟩
      · rw [Finset.mem_antidiagonal]
        omega
      · have hp := ih hi₀le
        have hq : (geometricPolynomial (2 ^ (n + 1))).coeff (m - i₀) = 1 := by
          rw [geometricPolynomial_coeff, if_pos hj₀]
        rw [hq, mul_one]
        exact hp

/-! ## The ordinary-closed counterexample

The gap register's *Why half-endpoint cells are needed* candidate: the
naive variant of the step approximant with ordinary closed-interval
indicators double-counts every shared cell endpoint, already giving the
value `2` instead of `1` at the origin for `n = 1`. -/

/-- The ordinary closed-interval indicator — the naive convention that
`halfEndpointIntervalIndicator` replaces. -/
noncomputable def closedIntervalIndicator (a b x : ℝ) : ℝ :=
  if a ≤ x ∧ x ≤ b then 1 else 0

/-- The naive step approximant: the same coefficients and normalization
as `stepApproximant`, with ordinary closed-interval indicators. -/
noncomputable def naiveStepApproximant (n : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ n / (2 : ℝ) ^ ((n + 1).choose 2) *
    ∑ m ∈ range (approximationDegree n + 1),
      ((approximationPolynomial n).coeff m : ℝ) *
        closedIntervalIndicator (stepIntervalLeft n m)
          (stepIntervalRight n m) x

/-- **The double-counting counterexample** (the register's candidate):
at `x = 0` the level-one cells `[-1/2, 0]` and `[0, 1/2]` each
contribute a full unit under the ordinary closed convention, so the
naive value is `2` — against `stepApproximant_one_zero`'s corrected
value `1`.  This is the elementary reason the half-endpoint convention
is needed. -/
theorem naiveStepApproximant_one_zero : naiveStepApproximant 1 0 = 2 := by
  have hp : approximationPolynomial 1 = 1 + X := by
    rw [show 1 = 0 + 1 by omega, approximationPolynomial_succ]
    simp
  rw [naiveStepApproximant]
  norm_num [approximationDegree, hp, stepIntervalLeft, stepIntervalRight,
    closedIntervalIndicator, Finset.sum_range_succ]
  norm_num [Polynomial.coeff_one]

end Fabius
