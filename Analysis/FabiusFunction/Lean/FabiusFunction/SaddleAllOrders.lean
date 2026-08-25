import FabiusFunction.QuantitativeSaddle

/-!
# Arbitrary-order Gaussian saddle-point bookkeeping

`FabiusFunction.QuantitativeSaddle` compares a rescaled saddle kernel with a
single Gaussian and extracts a relative `1 + O(1 / b)` estimate.  This module
raises the same comparison to every order.  On a central set the kernel is
still written as `K v = exp (-v ^ 2 / 2) * Complex.exp (E v)`, but the exact
exponent `E` is replaced by an arbitrary truncation `P`, and `Complex.exp P`
by its Taylor polynomial.  The governing estimate is the two-source bound

`‖exp E - sum_{q < m} P ^ q / q!‖ ≤ exp ‖P‖ * (2 * ‖E - P‖ + ‖P‖ ^ m)`,

valid whenever `‖E - P‖ ≤ 1`, which separates the error of truncating the
exponent from the Taylor remainder of the exponential.

Nothing here mentions the Fabius function or any particular saddle: the index
type `α`, the filter `l`, the comparison function `rate`, the central set and
the majorant are all parameters.  The module holds the generic
measure-theoretic bookkeeping -- pointwise majorant to `L¹` bound, `L¹` bound
to normalized-integral bound, central set plus complementary tail -- that
would otherwise be rewritten at every order by
`FabiusFunction.FabiusSaddleMassAllOrders`, its only consumer, which
instantiates it for the dyadic Lambert kernel on the way to the full Poincare
expansion of the normalized saddle-kernel mass.

## Main results

* `expTaylorPolynomial`, `gaussianExpTaylorReference` -- the truncation
  `sum_{q ∈ range m} z ^ q / q!` and its Gaussian-weighted form, which serves
  as the central reference.
* `norm_exp_sub_expTaylorPolynomial_le`, with Gaussian-weighted companion
  `norm_standardGaussian_mul_exp_sub_expTaylorPolynomial_le` -- the displayed
  two-source bound.
* `centralL1Error_isBigO_of_pointwise_majorant` -- a pointwise majorant on a
  measurable central set upgrades to an `L¹` big-`O` estimate there.
* `central_expTaylor_error_isBigO` -- the two previous steps combined.
* `normalizedIntegral_sub_reference_isBigO_of_L1` and its
  `..._of_central_tail` form -- transfer an `L¹` bound, respectively a central
  bound plus a complementary tail bound, to the normalized integrals of `K`
  and of the reference.
* `pairedReference`, `normalizedEvenExpansion` and
  `normalizedIntegral_sub_evenExpansion_isBigO` (with its central/tail
  variant) -- an optional parity layer: when the reference is grouped into
  even/odd pairs `eps ^ (2 * j) * A (2 * j) + eps ^ (2 * j + 1) * A (2 * j + 1)`
  and every odd-indexed coefficient is an odd function, the odd terms
  integrate away and only the even expansion survives.

## Conventions and caveats

`expTaylorPolynomial m` sums over `Finset.range m`, hence has degree `m - 1`
and is identically zero for `m = 0`; the remainder exponent in `‖P‖ ^ m`
follows that same indexing.  "Normalized" always means division by the
Gaussian mass `Real.sqrt (2 * Real.pi)`, never by the mass of the kernel
itself.  The central set is assumed only measurable, never an interval and
never bounded, and the representation `K = Gaussian * exp E` is assumed only
on it.  The constants are the sufficient ones produced by the triangle
inequality and `Complex.norm_exp_sub_one_le`; none of them is sharp.
-/

set_option autoImplicit false

open Filter MeasureTheory Set Asymptotics
open scoped Topology BigOperators

namespace Fabius.SaddleAllOrders

/-- The degree-`m-1` Taylor polynomial of the complex exponential. -/
noncomputable def expTaylorPolynomial (m : ℕ) (z : ℂ) : ℂ :=
  ∑ q ∈ Finset.range m, z ^ q / q.factorial

/-- A two-source arbitrary-order exponential remainder bound.  The first
term controls replacing the exact exponent `E` by a truncated exponent `P`;
the second is the Taylor remainder of `exp P` through degree `m-1`. -/
theorem norm_exp_sub_expTaylorPolynomial_le
    (m : ℕ) (E P : ℂ) (hsmall : ‖E - P‖ ≤ 1) :
    ‖Complex.exp E - expTaylorPolynomial m P‖ ≤
      Real.exp ‖P‖ * (2 * ‖E - P‖ + ‖P‖ ^ m) := by
  have hexact : Complex.exp E = Complex.exp P * Complex.exp (E - P) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hreplace :
      ‖Complex.exp E - Complex.exp P‖ ≤
        Real.exp ‖P‖ * (2 * ‖E - P‖) := by
    rw [hexact]
    calc
      ‖Complex.exp P * Complex.exp (E - P) - Complex.exp P‖ =
          ‖Complex.exp P * (Complex.exp (E - P) - 1)‖ := by
            congr 1
            ring
      _ = ‖Complex.exp P‖ * ‖Complex.exp (E - P) - 1‖ := norm_mul _ _
      _ ≤ Real.exp ‖P‖ * (2 * ‖E - P‖) :=
        mul_le_mul
          (Complex.norm_exp_le_exp_norm P)
          (Complex.norm_exp_sub_one_le hsmall)
          (norm_nonneg _) (Real.exp_nonneg _)
  have htaylor :
      ‖Complex.exp P - expTaylorPolynomial m P‖ ≤
        ‖P‖ ^ m * Real.exp ‖P‖ := by
    simpa only [expTaylorPolynomial] using
      Complex.norm_exp_sub_sum_le_norm_mul_exp P m
  calc
    ‖Complex.exp E - expTaylorPolynomial m P‖ ≤
        ‖Complex.exp E - Complex.exp P‖ +
          ‖Complex.exp P - expTaylorPolynomial m P‖ := by
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.exp ‖P‖ * (2 * ‖E - P‖) +
        ‖P‖ ^ m * Real.exp ‖P‖ := add_le_add hreplace htaylor
    _ = Real.exp ‖P‖ * (2 * ‖E - P‖ + ‖P‖ ^ m) := by ring

/-- Gaussian-weighted version of the arbitrary-order exponential remainder.
This is the pointwise analytic estimate consumed by central-arc dominated
integration arguments. -/
theorem norm_standardGaussian_mul_exp_sub_expTaylorPolynomial_le
    (m : ℕ) (E P : ℂ) (v : ℝ) (hsmall : ‖E - P‖ ≤ 1) :
    ‖QuantitativeSaddle.standardGaussian v * Complex.exp E -
        QuantitativeSaddle.standardGaussian v * expTaylorPolynomial m P‖ ≤
      Real.exp (-(v ^ 2) / 2) * Real.exp ‖P‖ *
        (2 * ‖E - P‖ + ‖P‖ ^ m) := by
  rw [← mul_sub, norm_mul]
  have hG : ‖QuantitativeSaddle.standardGaussian v‖ =
      Real.exp (-(v ^ 2) / 2) := by
    simp only [QuantitativeSaddle.standardGaussian, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hG]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (norm_exp_sub_expTaylorPolynomial_le m E P hsmall)
      (Real.exp_nonneg (-(v ^ 2) / 2))

/-- The Gaussian-weighted Taylor polynomial used as a central saddle
reference. -/
noncomputable def gaussianExpTaylorReference (m : ℕ) (P : ℝ → ℂ)
    (v : ℝ) : ℂ :=
  QuantitativeSaddle.standardGaussian v * expTaylorPolynomial m (P v)

/-- Turn a pointwise central-set majorant into an `L¹` asymptotic estimate.
All measurability and domination assumptions are explicit, so this lemma is
usable with order-dependent polynomial-Gaussian majorants. -/
theorem centralL1Error_isBigO_of_pointwise_majorant
    {α : Type*} (l : Filter α) (rate : α → ℝ)
    (K reference : α → ℝ → ℂ) (central : α → Set ℝ)
    (major : α → ℝ → ℝ)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l, Integrable (reference i))
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hmajorInt : ∀ᶠ i in l, IntegrableOn (major i) (central i))
    (hmajorNonneg : ∀ᶠ i in l, ∀ v ∈ central i, 0 ≤ major i v)
    (hbound : ∀ᶠ i in l, ∀ v ∈ central i,
      ‖K i v - reference i v‖ ≤ major i v)
    (hmajor : (fun i ↦ ∫ v in central i, major i v) =O[l] rate) :
    (fun i ↦ ∫ v in central i, ‖K i v - reference i v‖) =O[l] rate := by
  have hdom :
      (fun i ↦ ∫ v in central i, ‖K i v - reference i v‖) =O[l]
        (fun i ↦ ∫ v in central i, major i v) := by
    apply IsBigO.of_bound 1
    filter_upwards [hK, hreference, hcentralMeas, hmajorInt,
        hmajorNonneg, hbound] with i hKi hRi hmeas hMi hMnonneg hi
    have hdiff : IntegrableOn (fun v ↦ ‖K i v - reference i v‖) (central i) :=
      (hKi.sub hRi).norm.integrableOn
    have hle :
        (∫ v in central i, ‖K i v - reference i v‖) ≤
          ∫ v in central i, major i v :=
      setIntegral_mono_on hdiff hMi hmeas hi
    have hdiffNonneg : 0 ≤ ∫ v in central i,
        ‖K i v - reference i v‖ :=
      integral_nonneg fun _ ↦ norm_nonneg _
    have hMNonneg : 0 ≤ ∫ v in central i, major i v := by
      exact setIntegral_nonneg hmeas hMnonneg
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hdiffNonneg, abs_of_nonneg hMNonneg, one_mul]
    exact hle
  exact hdom.trans hmajor

/-- Arbitrary-order central saddle estimate from a truncated exponent and its
explicit Gaussian-weighted remainder majorant. -/
theorem central_expTaylor_error_isBigO
    {α : Type*} (l : Filter α) (m : ℕ) (rate : α → ℝ)
    (K : α → ℝ → ℂ) (E P : α → ℝ → ℂ)
    (central : α → Set ℝ)
    (major : α → ℝ → ℝ)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l,
      Integrable (gaussianExpTaylorReference m (P i)))
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hmajorInt : ∀ᶠ i in l, IntegrableOn (major i) (central i))
    (hmajorNonneg : ∀ᶠ i in l, ∀ v ∈ central i, 0 ≤ major i v)
    (hrepresentation : ∀ᶠ i in l, ∀ v ∈ central i,
      K i v = QuantitativeSaddle.standardGaussian v * Complex.exp (E i v))
    (hsmall : ∀ᶠ i in l, ∀ v ∈ central i, ‖E i v - P i v‖ ≤ 1)
    (hmajorBound : ∀ᶠ i in l, ∀ v ∈ central i,
      Real.exp (-(v ^ 2) / 2) * Real.exp ‖P i v‖ *
          (2 * ‖E i v - P i v‖ + ‖P i v‖ ^ m) ≤ major i v)
    (hmajor : (fun i ↦ ∫ v in central i, major i v) =O[l] rate) :
    (fun i ↦ ∫ v in central i,
      ‖K i v - gaussianExpTaylorReference m (P i) v‖) =O[l] rate := by
  apply centralL1Error_isBigO_of_pointwise_majorant l rate K
    (fun i ↦ gaussianExpTaylorReference m (P i)) central major
    hK hreference hcentralMeas hmajorInt hmajorNonneg
  · filter_upwards [hrepresentation, hsmall, hmajorBound] with
      i hrepr hsmalli hmajori
    intro v hv
    rw [hrepr v hv]
    exact (norm_standardGaussian_mul_exp_sub_expTaylorPolynomial_le
      m (E i v) (P i v) v (hsmalli v hv)).trans (hmajori v hv)
  · exact hmajor

/-- The paired truncation
`sum j <= N, eps^(2j) A_(2j) + eps^(2j+1) A_(2j+1)`.

Writing the truncation in even/odd pairs makes the cancellation of every odd
term under integration explicit. -/
noncomputable def pairedReference (N : ℕ) (eps : ℝ)
    (A : ℕ → ℝ → ℂ) (v : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    ((eps : ℂ) ^ (2 * j) * A (2 * j) v +
      (eps : ℂ) ^ (2 * j + 1) * A (2 * j + 1) v)

/-- The normalized even part of the integrated paired truncation. -/
noncomputable def normalizedEvenExpansion (N : ℕ) (eps : ℝ)
    (A : ℕ → ℝ → ℂ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
    ∑ j ∈ Finset.range (N + 1),
      ((eps : ℂ) ^ (2 * j) * ∫ v : ℝ, A (2 * j) v)

lemma integrable_pairedReference (N : ℕ) (eps : ℝ)
    (A : ℕ → ℝ → ℂ)
    (hA : ∀ k < 2 * (N + 1), Integrable (A k)) :
    Integrable (pairedReference N eps A) := by
  unfold pairedReference
  apply integrable_finsetSum
  intro j hj
  have hjN : j < N + 1 := Finset.mem_range.mp hj
  exact ((hA (2 * j) (by omega)).const_mul _).add
    ((hA (2 * j + 1) (by omega)).const_mul _)

lemma integral_pairedReference_eq_even
    (N : ℕ) (eps : ℝ) (A : ℕ → ℝ → ℂ)
    (hA : ∀ k < 2 * (N + 1), Integrable (A k))
    (hodd : ∀ j < N + 1, Function.Odd (A (2 * j + 1))) :
    (∫ v : ℝ, pairedReference N eps A v) =
      ∑ j ∈ Finset.range (N + 1),
        (eps : ℂ) ^ (2 * j) * ∫ v : ℝ, A (2 * j) v := by
  unfold pairedReference
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N + 1 := Finset.mem_range.mp hj
    rw [integral_add]
    · rw [integral_const_mul, integral_const_mul,
          QuantitativeSaddle.integral_eq_zero_of_odd _ (hodd j hjN)]
      simp
    · exact (hA (2 * j) (by omega)).const_mul _
    · exact (hA (2 * j + 1) (by omega)).const_mul _
  · intro j hj
    have hjN : j < N + 1 := Finset.mem_range.mp hj
    exact ((hA (2 * j) (by omega)).const_mul _).add
      ((hA (2 * j + 1) (by omega)).const_mul _)

/-- An `L¹` approximation of a kernel by any integrable reference gives the
same-order approximation of their normalized integrals. -/
theorem normalizedIntegral_sub_reference_isBigO_of_L1
    {α : Type*} (l : Filter α) (rate : α → ℝ)
    (K reference : α → ℝ → ℂ)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l, Integrable (reference i))
    (herror : (fun i ↦ ∫ v : ℝ, ‖K i v - reference i v‖) =O[l] rate) :
    (fun i ↦
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) -
        (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
          (∫ v : ℝ, reference i v)) =O[l] rate := by
  rw [isBigO_iff] at herror ⊢
  obtain ⟨C, hC⟩ := herror
  let gaussianMass : ℝ := Real.sqrt (2 * Real.pi)
  have hmass : 0 < gaussianMass := by
    dsimp [gaussianMass]
    positivity
  refine ⟨gaussianMass⁻¹ * C, ?_⟩
  filter_upwards [hK, hreference, hC] with i hKi hRi hi
  have hdiffInt : Integrable (fun v ↦ ‖K i v - reference i v‖) :=
    (hKi.sub hRi).norm
  have hnonneg : 0 ≤ ∫ v : ℝ, ‖K i v - reference i v‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hi
  have hnorm :
      ‖(∫ v : ℝ, K i v) - ∫ v : ℝ, reference i v‖ ≤
        ∫ v : ℝ, ‖K i v - reference i v‖ := by
    rw [← integral_sub hKi hRi]
    exact norm_integral_le_of_norm_le hdiffInt
      (Filter.Eventually.of_forall fun _ ↦ le_rfl)
  change ‖(gaussianMass : ℂ)⁻¹ * (∫ v : ℝ, K i v) -
      (gaussianMass : ℂ)⁻¹ * (∫ v : ℝ, reference i v)‖ ≤ _
  rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hmass]
  calc
    gaussianMass⁻¹ *
          ‖(∫ v : ℝ, K i v) - ∫ v : ℝ, reference i v‖
        ≤ gaussianMass⁻¹ *
          (∫ v : ℝ, ‖K i v - reference i v‖) := by gcongr
    _ ≤ gaussianMass⁻¹ * (C * ‖rate i‖) := by gcongr
    _ = (gaussianMass⁻¹ * C) * ‖rate i‖ := by ring

/-- Central-set plus complementary-tail form of the arbitrary-reference
normalized-integral estimate. -/
theorem normalizedIntegral_sub_reference_isBigO_of_central_tail
    {α : Type*} (l : Filter α) (rate : α → ℝ)
    (K reference : α → ℝ → ℂ) (central : α → Set ℝ)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hreference : ∀ᶠ i in l, Integrable (reference i))
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hcentral :
      (fun i ↦ ∫ v in central i, ‖K i v - reference i v‖) =O[l] rate)
    (htail :
      (fun i ↦ ∫ v in (central i)ᶜ, ‖K i v - reference i v‖) =O[l] rate) :
    (fun i ↦
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) -
        (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
          (∫ v : ℝ, reference i v)) =O[l] rate := by
  apply normalizedIntegral_sub_reference_isBigO_of_L1 l rate K reference
    hK hreference
  have hsum := hcentral.add htail
  apply hsum.congr'
  · filter_upwards [hK, hreference, hcentralMeas] with i hKi hRi hmeas
    have hdiffInt : Integrable (fun v ↦ ‖K i v - reference i v‖) :=
      (hKi.sub hRi).norm
    exact integral_add_compl hmeas hdiffInt
  · exact Filter.EventuallyEq.rfl

/-- All-orders parity wrapper.  If a kernel is `L¹`-close through degree
`2N+1` to a paired Edgeworth reference, then only the even coefficients
survive integration and the normalized remainder has the same order. -/
theorem normalizedIntegral_sub_evenExpansion_isBigO
    {α : Type*} (l : Filter α) (N : ℕ) (eps rate : α → ℝ)
    (K : α → ℝ → ℂ) (A : ℕ → ℝ → ℂ)
    (hA : ∀ k < 2 * (N + 1), Integrable (A k))
    (hodd : ∀ j < N + 1, Function.Odd (A (2 * j + 1)))
    (hK : ∀ᶠ i in l, Integrable (K i))
    (herror :
      (fun i ↦ ∫ v : ℝ, ‖K i v - pairedReference N (eps i) A v‖)
        =O[l] rate) :
    (fun i ↦
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) -
        normalizedEvenExpansion N (eps i) A) =O[l] rate := by
  have hreference : ∀ᶠ i in l,
      Integrable (pairedReference N (eps i) A) :=
    Filter.Eventually.of_forall fun i ↦ integrable_pairedReference N (eps i) A hA
  have h := normalizedIntegral_sub_reference_isBigO_of_L1 l rate K
    (fun i ↦ pairedReference N (eps i) A) hK hreference herror
  apply h.congr'
  · filter_upwards with i
    rw [integral_pairedReference_eq_even N (eps i) A hA hodd]
    rfl
  · exact Filter.EventuallyEq.rfl

/-- Central/tail form of `normalizedIntegral_sub_evenExpansion_isBigO`. -/
theorem normalizedIntegral_sub_evenExpansion_isBigO_of_central_tail
    {α : Type*} (l : Filter α) (N : ℕ) (eps rate : α → ℝ)
    (K : α → ℝ → ℂ) (A : ℕ → ℝ → ℂ)
    (central : α → Set ℝ)
    (hA : ∀ k < 2 * (N + 1), Integrable (A k))
    (hodd : ∀ j < N + 1, Function.Odd (A (2 * j + 1)))
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hcentral :
      (fun i ↦ ∫ v in central i,
        ‖K i v - pairedReference N (eps i) A v‖) =O[l] rate)
    (htail :
      (fun i ↦ ∫ v in (central i)ᶜ,
        ‖K i v - pairedReference N (eps i) A v‖) =O[l] rate) :
    (fun i ↦
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) -
        normalizedEvenExpansion N (eps i) A) =O[l] rate := by
  have hreference : ∀ᶠ i in l,
      Integrable (pairedReference N (eps i) A) :=
    Filter.Eventually.of_forall fun i ↦ integrable_pairedReference N (eps i) A hA
  have h := normalizedIntegral_sub_reference_isBigO_of_central_tail l rate K
    (fun i ↦ pairedReference N (eps i) A) central hK hreference
    hcentralMeas hcentral htail
  apply h.congr'
  · filter_upwards with i
    rw [integral_pairedReference_eq_even N (eps i) A hA hodd]
    rfl
  · exact Filter.EventuallyEq.rfl

end Fabius.SaddleAllOrders
