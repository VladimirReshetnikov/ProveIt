import FabiusFunction.FabiusLegendreTranslateBlocks
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Rvachev-translate Legendre series and its fixed-scale partial sums

The finite translate block `rvachevLegendreTranslateBlock F n` agrees on
`[-1, 1]` with the `n`-th even Fourier--Legendre block.  This file transports
the existing Legendre convergence theorems across that equality, while
retaining every finite train as one outer-series term.

It also synthesizes the whole `N`-th Legendre partial sum at the single mesh
`4 ^ N`.  Its deconvolution polynomial is sampled once on that common mesh;
the resulting finite train agrees both with the polynomial partial sum and
with the sum of the separately synthesized blocks.  These are equalities of
functions on `[-1, 1]`, not equalities of the two coefficient vectors.
-/

set_option autoImplicit false

open Filter Polynomial Set Finset
open scoped BigOperators Topology

namespace Fabius

noncomputable section

/-! ## The literal outer translate-block series -/

/-- The literal finite translate blocks are absolutely summable at every
point of `[-1,1]` when they are retained as outer-series terms. -/
theorem summable_norm_rvachevLegendreTranslateBlock
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    Summable (fun n : ℕ => ‖rvachevLegendreTranslateBlock F n x‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_abs_rvachevLegendreCoefficient F hF)
  rw [rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock F hF n hx]
  change ‖rvachevLegendreCoefficient F n *
      (legendrePolynomial (2 * n)).eval x‖ ≤
    |rvachevLegendreCoefficient F n|
  rw [norm_mul]
  simp only [Real.norm_eq_abs]
  calc
    |rvachevLegendreCoefficient F n| *
          |(legendrePolynomial (2 * n)).eval x| ≤
        |rvachevLegendreCoefficient F n| * 1 :=
      mul_le_mul_of_nonneg_left
        (abs_eval_legendrePolynomial_le_one (2 * n) x hx) (abs_nonneg _)
    _ = |rvachevLegendreCoefficient F n| := mul_one _

/-- Summability of the literal translate-block series at every point of
`[-1,1]`, deduced from absolute summability. -/
theorem summable_rvachevLegendreTranslateBlock
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    Summable (fun n : ℕ => rvachevLegendreTranslateBlock F n x) :=
  Summable.of_norm (summable_norm_rvachevLegendreTranslateBlock F hF x hx)

/-- **Blockwise Legendre--Rvachev loop.**  On `[-1,1]`, the outer series of
literal finite shifted-`up` trains sums to `rvachevUp`. -/
theorem hasSum_rvachevLegendreTranslateBlock
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n : ℕ => rvachevLegendreTranslateBlock F n x)
      (rvachevUp F x) := by
  exact (hasSum_rvachevLegendreSeries F hF x hx).congr_fun fun n => by
    simpa only [rvachevLegendreBlock] using
      rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock F hF n hx

/-- `tsum` form of the blockwise Legendre--Rvachev loop. -/
theorem tsum_rvachevLegendreTranslateBlock
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    (∑' n : ℕ, rvachevLegendreTranslateBlock F n x) = rvachevUp F x :=
  (hasSum_rvachevLegendreTranslateBlock F hF x hx).tsum_eq

/-! ## One common mesh for a whole partial sum -/

/-- The Rvachev deconvolution `C_N = D(S_N)` of the `N`-th even Legendre
partial-sum polynomial. -/
noncomputable def rvachevLegendrePartialSumDeconvolutionPolynomial
    (F : BoundedFabius) (N : ℕ) : ℝ[X] :=
  rvachevDeconvolvedPolynomial (rvachevLegendrePartialSumPolynomial F N)

/-- Deconvolution preserves the exact degree of every Legendre partial-sum
polynomial, including degenerate partial sums whose visible degree drops. -/
@[simp]
theorem natDegree_rvachevLegendrePartialSumDeconvolutionPolynomial
    (F : BoundedFabius) (N : ℕ) :
    (rvachevLegendrePartialSumDeconvolutionPolynomial F N).natDegree =
      (rvachevLegendrePartialSumPolynomial F N).natDegree := by
  simp [rvachevLegendrePartialSumDeconvolutionPolynomial]

/-- Deconvolution preserves the leading coefficient of every Legendre
partial-sum polynomial. -/
@[simp]
theorem leadingCoeff_rvachevLegendrePartialSumDeconvolutionPolynomial
    (F : BoundedFabius) (N : ℕ) :
    (rvachevLegendrePartialSumDeconvolutionPolynomial F N).leadingCoeff =
      (rvachevLegendrePartialSumPolynomial F N).leadingCoeff := by
  simp [rvachevLegendrePartialSumDeconvolutionPolynomial]

/-- Linearity of Rvachev deconvolution identifies `C_N` with the finite sum
of the separately deconvolved even Legendre modes. -/
theorem rvachevLegendrePartialSumDeconvolutionPolynomial_eq_sum
    (F : BoundedFabius) (N : ℕ) :
    rvachevLegendrePartialSumDeconvolutionPolynomial F N =
      ∑ n ∈ range (N + 1),
        C (rvachevLegendreCoefficient F n) *
          rvachevLegendreDeconvolutionPolynomial (2 * n) := by
  rw [rvachevLegendrePartialSumDeconvolutionPolynomial,
    ← rvachevDeconvolutionLinearMap_apply,
    rvachevLegendrePartialSumPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← smul_eq_C_mul, map_smul, rvachevDeconvolutionLinearMap_apply,
    smul_eq_C_mul, rvachevLegendreDeconvolutionPolynomial]

/-- The coefficient of the translate indexed by `k` when the entire `N`-th
Legendre partial sum is synthesized at the common mesh `4 ^ N`. -/
noncomputable def rvachevLegendrePartialSumAtomCoefficient
    (F : BoundedFabius) (N : ℕ) (k : ℤ) : ℝ :=
  (rvachevLegendreScale N : ℝ)⁻¹ *
    (rvachevLegendrePartialSumDeconvolutionPolynomial F N).eval
      ((k : ℝ) / (rvachevLegendreScale N : ℝ))

/-- Expanded common-mesh coefficient: every mode is deconvolved separately,
but all of them are sampled at the single finest mesh `4 ^ N`. -/
theorem rvachevLegendrePartialSumAtomCoefficient_eq_sum
    (F : BoundedFabius) (N : ℕ) (k : ℤ) :
    rvachevLegendrePartialSumAtomCoefficient F N k =
      ∑ n ∈ range (N + 1),
        rvachevLegendreCoefficient F n /
            (rvachevLegendreScale N : ℝ) *
          (rvachevLegendreDeconvolutionPolynomial (2 * n)).eval
            ((k : ℝ) / (rvachevLegendreScale N : ℝ)) := by
  rw [rvachevLegendrePartialSumAtomCoefficient,
    rvachevLegendrePartialSumDeconvolutionPolynomial_eq_sum,
    Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- The single-mesh finite shifted-`up` train realizing the whole `N`-th
even Legendre partial sum. -/
noncomputable def rvachevLegendrePartialSumTranslateBlock
    (F : BoundedFabius) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ rvachevLegendreIndexSet N,
    rvachevLegendrePartialSumAtomCoefficient F N k *
      rvachevUp F
        (x - (k : ℝ) / (rvachevLegendreScale N : ℝ))

private theorem rvachevLegendreScale_ne_zero (N : ℕ) :
    rvachevLegendreScale N ≠ 0 := by
  simp [rvachevLegendreScale]

private theorem rvachevLegendrePartialSumPolynomial_natDegree_le_padicVal
    (F : BoundedFabius) (N : ℕ) :
    (rvachevLegendrePartialSumPolynomial F N).natDegree ≤
      padicValNat 2 (rvachevLegendreScale N) := by
  have hfour : rvachevLegendreScale N = 2 ^ (2 * N) := by
    simp only [rvachevLegendreScale]
    calc
      (4 ^ N : ℕ) = (2 ^ 2) ^ N := by norm_num
      _ = 2 ^ (2 * N) := by rw [pow_mul]
  calc
    (rvachevLegendrePartialSumPolynomial F N).natDegree ≤ 2 * N :=
      rvachevLegendrePartialSumPolynomial_natDegree_le F N
    _ = padicValNat 2 (rvachevLegendreScale N) := by
      rw [hfour, padicValNat.prime_pow]

/-- **Global fixed-scale synthesis.**  The whole `N`-th Legendre partial sum
is reconstructed by the common mesh `4 ^ N` at every real input.  Globally
the compactly supported atom train is expressed as a `tsum`. -/
theorem eval_rvachevLegendrePartialSumPolynomial_eq_tsum_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) (x : ℝ) :
    (rvachevLegendrePartialSumPolynomial F N).eval x =
      (rvachevLegendreScale N : ℝ)⁻¹ *
        ∑' k : ℤ,
          (rvachevLegendrePartialSumDeconvolutionPolynomial F N).eval
              ((k : ℝ) / (rvachevLegendreScale N : ℝ)) *
            rvachevUp F
              (x - (k : ℝ) / (rvachevLegendreScale N : ℝ)) := by
  have hsynth :=
    normalized_tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
      F hF (rvachevLegendreScale_ne_zero N)
        (rvachevLegendrePartialSumPolynomial_natDegree_le_padicVal F N) x
  simpa only [rvachevLegendrePartialSumDeconvolutionPolynomial] using
    hsynth.symm

/-- **Finite fixed-scale synthesis on `[-1,1]`.**  The whole `N`-th Legendre
partial sum is reconstructed from the common open atom block
`(-2 * 4^N, 2 * 4^N)`. -/
theorem eval_rvachevLegendrePartialSumPolynomial_eq_sum_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (rvachevLegendrePartialSumPolynomial F N).eval x =
      (rvachevLegendreScale N : ℝ)⁻¹ *
        ∑ k ∈ rvachevLegendreIndexSet N,
          (rvachevLegendrePartialSumDeconvolutionPolynomial F N).eval
              ((k : ℝ) / (rvachevLegendreScale N : ℝ)) *
            rvachevUp F
              (x - (k : ℝ) / (rvachevLegendreScale N : ℝ)) := by
  have hsynth :=
    normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
      F hF (rvachevLegendreScale_ne_zero N)
        (rvachevLegendrePartialSumPolynomial_natDegree_le_padicVal F N) hx
  simpa only [rvachevLegendrePartialSumDeconvolutionPolynomial,
    rvachevLegendreIndexSet] using hsynth.symm

/-- On `[-1,1]`, the single-mesh translate train is exactly the polynomial
Legendre partial sum. -/
theorem rvachevLegendrePartialSumTranslateBlock_eq_eval_partialSumPolynomial
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    rvachevLegendrePartialSumTranslateBlock F N x =
      (rvachevLegendrePartialSumPolynomial F N).eval x := by
  rw [rvachevLegendrePartialSumTranslateBlock,
    eval_rvachevLegendrePartialSumPolynomial_eq_sum_rvachevUp F hF N hx,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [rvachevLegendrePartialSumAtomCoefficient]
  ring

/-- The fixed-scale train and the sum of the separately scaled finite blocks
realize the same partial-sum function on `[-1,1]`.  This does not assert that
their coefficient vectors agree. -/
theorem rvachevLegendrePartialSumTranslateBlock_eq_sum_translateBlock
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    rvachevLegendrePartialSumTranslateBlock F N x =
      ∑ n ∈ range (N + 1), rvachevLegendreTranslateBlock F n x := by
  rw [rvachevLegendrePartialSumTranslateBlock_eq_eval_partialSumPolynomial
    F hF N hx, eval_rvachevLegendrePartialSumPolynomial]
  apply Finset.sum_congr rfl
  intro n _hn
  symm
  simpa only [rvachevLegendreBlock] using
    rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock F hF n hx

/-! ## Literal uniform convergence on the Legendre interval -/

/-- The literal finite translate block, bundled as a continuous function on
`[-1,1]`.  Continuity follows there from its equality with the corresponding
polynomial Legendre block. -/
noncomputable def rvachevLegendreTranslateBlockOnInterval
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    C(Icc (-1 : ℝ) 1, ℝ) :=
  ⟨fun x => rvachevLegendreTranslateBlock F n x, by
    have heq :
        (fun x : Icc (-1 : ℝ) 1 => rvachevLegendreTranslateBlock F n x) =
          fun x : Icc (-1 : ℝ) 1 => rvachevLegendreBlock F n x := by
      funext x
      exact rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock
        F hF n x.property
    rw [heq]
    exact continuous_const.mul
      ((legendrePolynomial_contDiff (2 * n)).continuous.comp
        continuous_subtype_val)⟩

/-- Evaluation of the bundled literal translate block. -/
@[simp]
theorem rvachevLegendreTranslateBlockOnInterval_apply
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ)
    (x : Icc (-1 : ℝ) 1) :
    rvachevLegendreTranslateBlockOnInterval F hF n x =
      rvachevLegendreTranslateBlock F n x :=
  rfl

/-- On the Legendre interval, the bundled literal translate block equals the
usual scalar multiple of the even Legendre polynomial. -/
theorem rvachevLegendreTranslateBlockOnInterval_eq_smul
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    rvachevLegendreTranslateBlockOnInterval F hF n =
      rvachevLegendreCoefficient F n •
        continuousMapOnLegendreInterval
          (fun x : ℝ => (legendrePolynomial (2 * n)).eval x)
          (legendrePolynomial_contDiff (2 * n)).continuous := by
  ext x
  simp only [rvachevLegendreTranslateBlockOnInterval_apply,
    ContinuousMap.smul_apply, smul_eq_mul,
    continuousMapOnLegendreInterval_apply]
  simpa only [rvachevLegendreBlock] using
    rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock
      F hF n x.property

/-- Absolute summability in the supremum norm of continuous functions on
`[-1,1]`.  This is the literal blockwise Weierstrass bound. -/
theorem summable_norm_rvachevLegendreTranslateBlockOnInterval
    (F : BoundedFabius) (hF : IsFabius F) :
    Summable (fun n : ℕ =>
      ‖rvachevLegendreTranslateBlockOnInterval F hF n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_abs_rvachevLegendreCoefficient F hF)
  rw [rvachevLegendreTranslateBlockOnInterval_eq_smul, norm_smul,
    Real.norm_eq_abs]
  have hpoly :
      ‖continuousMapOnLegendreInterval
          (fun x : ℝ => (legendrePolynomial (2 * n)).eval x)
          (legendrePolynomial_contDiff (2 * n)).continuous‖ ≤ 1 := by
    rw [ContinuousMap.norm_le _ zero_le_one]
    intro x
    simpa only [continuousMapOnLegendreInterval_apply, Real.norm_eq_abs] using
      abs_eval_legendrePolynomial_le_one (2 * n) x x.property
  calc
    |rvachevLegendreCoefficient F n| *
          ‖continuousMapOnLegendreInterval
            (fun x : ℝ => (legendrePolynomial (2 * n)).eval x)
            (legendrePolynomial_contDiff (2 * n)).continuous‖ ≤
        |rvachevLegendreCoefficient F n| * 1 :=
      mul_le_mul_of_nonneg_left hpoly (abs_nonneg _)
    _ = |rvachevLegendreCoefficient F n| := mul_one _

/-- Summability in the continuous-map Banach space, deduced from supremum-norm
summability. -/
theorem summable_rvachevLegendreTranslateBlockOnInterval
    (F : BoundedFabius) (hF : IsFabius F) :
    Summable (fun n : ℕ =>
      rvachevLegendreTranslateBlockOnInterval F hF n) :=
  Summable.of_norm
    (summable_norm_rvachevLegendreTranslateBlockOnInterval F hF)

/-- The literal translate blocks converge uniformly on `[-1,1]` to
`rvachevUp`, expressed as a `HasSum` in the continuous-map Banach space. -/
theorem hasSum_rvachevLegendreTranslateBlock_uniform
    (F : BoundedFabius) (hF : IsFabius F) :
    HasSum (fun n : ℕ => rvachevLegendreTranslateBlockOnInterval F hF n)
      (continuousMapOnLegendreInterval
        (rvachevUp F) (rvachev_contDiff F hF).continuous) := by
  exact (hasSum_rvachevLegendreSeries_uniform F hF).congr_fun fun n =>
    rvachevLegendreTranslateBlockOnInterval_eq_smul F hF n

/-- Uniform `tsum` equality for the literal translate-block series. -/
theorem tsum_rvachevLegendreTranslateBlock_uniform
    (F : BoundedFabius) (hF : IsFabius F) :
    (∑' n : ℕ, rvachevLegendreTranslateBlockOnInterval F hF n) =
      continuousMapOnLegendreInterval
        (rvachevUp F) (rvachev_contDiff F hF).continuous :=
  (hasSum_rvachevLegendreTranslateBlock_uniform F hF).tsum_eq

/-! ## Uniform convergence of the common-mesh partial trains -/

/-- The common-mesh finite train for the `N`-th Legendre partial sum, bundled
as a continuous function on `[-1,1]`.  Continuity follows from its equality
there with the polynomial partial sum. -/
noncomputable def rvachevLegendrePartialSumTranslateBlockOnInterval
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    C(Icc (-1 : ℝ) 1, ℝ) :=
  ⟨fun x => rvachevLegendrePartialSumTranslateBlock F N x, by
    have heq :
        (fun x : Icc (-1 : ℝ) 1 =>
          rvachevLegendrePartialSumTranslateBlock F N x) =
          fun x : Icc (-1 : ℝ) 1 =>
            (rvachevLegendrePartialSumPolynomial F N).eval (x : ℝ) := by
      funext x
      exact rvachevLegendrePartialSumTranslateBlock_eq_eval_partialSumPolynomial
        F hF N x.property
    rw [heq]
    exact (rvachevLegendrePartialSumPolynomial F N).continuous.comp
      continuous_subtype_val⟩

/-- Evaluation of the bundled common-mesh partial train. -/
@[simp]
theorem rvachevLegendrePartialSumTranslateBlockOnInterval_apply
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ)
    (x : Icc (-1 : ℝ) 1) :
    rvachevLegendrePartialSumTranslateBlockOnInterval F hF N x =
      rvachevLegendrePartialSumTranslateBlock F N x :=
  rfl

/-- The bundled common-mesh train is the polynomial Legendre partial sum on
`[-1,1]`. -/
theorem rvachevLegendrePartialSumTranslateBlockOnInterval_eq_eval_partialSumPolynomial
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    rvachevLegendrePartialSumTranslateBlockOnInterval F hF N =
      continuousMapOnLegendreInterval
        (fun x : ℝ => (rvachevLegendrePartialSumPolynomial F N).eval x)
        (rvachevLegendrePartialSumPolynomial F N).continuous := by
  ext x
  simp only [rvachevLegendrePartialSumTranslateBlockOnInterval_apply,
    continuousMapOnLegendreInterval_apply]
  exact rvachevLegendrePartialSumTranslateBlock_eq_eval_partialSumPolynomial
    F hF N x.property

/-- The bundled common-mesh train is also the sum of the separately scaled
literal translate blocks through level `N`. -/
theorem rvachevLegendrePartialSumTranslateBlockOnInterval_eq_sum
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    rvachevLegendrePartialSumTranslateBlockOnInterval F hF N =
      ∑ n ∈ range (N + 1),
        rvachevLegendreTranslateBlockOnInterval F hF n := by
  apply ContinuousMap.ext
  intro x
  rw [rvachevLegendrePartialSumTranslateBlockOnInterval_apply]
  change rvachevLegendrePartialSumTranslateBlock F N x =
    (ContinuousMap.evalAlgHom ℝ ℝ x)
      (∑ n ∈ range (N + 1),
        rvachevLegendreTranslateBlockOnInterval F hF n)
  rw [map_sum]
  change rvachevLegendrePartialSumTranslateBlock F N x =
    ∑ n ∈ range (N + 1),
      rvachevLegendreTranslateBlockOnInterval F hF n x
  simp only [rvachevLegendreTranslateBlockOnInterval_apply]
  exact rvachevLegendrePartialSumTranslateBlock_eq_sum_translateBlock
    F hF N x.property

/-- The one-mesh Legendre partial trains converge to `rvachevUp` in the
supremum norm on `[-1,1]`. -/
theorem tendsto_rvachevLegendrePartialSumTranslateBlockOnInterval
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto
      (fun N : ℕ =>
        rvachevLegendrePartialSumTranslateBlockOnInterval F hF N)
      atTop
      (𝓝 (continuousMapOnLegendreInterval
        (rvachevUp F) (rvachev_contDiff F hF).continuous)) := by
  have h :=
    (hasSum_rvachevLegendreTranslateBlock_uniform F hF).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
  refine h.congr' (Filter.Eventually.of_forall fun N => ?_)
  simp only [Function.comp_apply]
  exact
    (rvachevLegendrePartialSumTranslateBlockOnInterval_eq_sum F hF N).symm

/-- Raw function form of uniform convergence of the one-mesh Legendre
partial trains on `[-1,1]`. -/
theorem rvachevLegendrePartialSumTranslateBlock_tendstoUniformlyOn
    (F : BoundedFabius) (hF : IsFabius F) :
    TendstoUniformlyOn
      (fun N : ℕ => rvachevLegendrePartialSumTranslateBlock F N)
      (rvachevUp F) atTop (Icc (-1 : ℝ) 1) := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have h := ContinuousMap.tendsto_iff_tendstoUniformly.mp
    (tendsto_rvachevLegendrePartialSumTranslateBlockOnInterval F hF)
  have happrox :
      (fun N (x : Icc (-1 : ℝ) 1) =>
        rvachevLegendrePartialSumTranslateBlockOnInterval F hF N x) =ᶠ[atTop]
        fun N (x : Icc (-1 : ℝ) 1) =>
          rvachevLegendrePartialSumTranslateBlock F N x :=
    Filter.Eventually.of_forall fun N => by
      funext x
      exact rvachevLegendrePartialSumTranslateBlockOnInterval_apply F hF N x
  have h' := (tendstoUniformly_congr happrox).mp h
  have hlim :
      rvachevUp F ∘ Subtype.val =
        ⇑(continuousMapOnLegendreInterval
          (rvachevUp F) (rvachev_contDiff F hF).continuous) := by
    funext x
    exact (continuousMapOnLegendreInterval_apply
      (rvachevUp F) (rvachev_contDiff F hF).continuous x).symm
  rw [hlim]
  exact h'

/-- The supremum norm of the error of the bundled common-mesh train tends to
zero on `[-1,1]`. -/
theorem tendsto_norm_rvachevLegendrePartialSumTranslateBlockOnInterval_sub
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto
      (fun N : ℕ =>
        ‖rvachevLegendrePartialSumTranslateBlockOnInterval F hF N -
          continuousMapOnLegendreInterval
            (rvachevUp F) (rvachev_contDiff F hF).continuous‖)
      atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp
    (tendsto_rvachevLegendrePartialSumTranslateBlockOnInterval F hF)

/-- Pointwise consequence on `[-1,1]` of uniform convergence of the
common-mesh Legendre partial trains. -/
theorem tendsto_rvachevLegendrePartialSumTranslateBlock
    (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun N : ℕ => rvachevLegendrePartialSumTranslateBlock F N x)
      atTop (𝓝 (rvachevUp F x)) :=
  (rvachevLegendrePartialSumTranslateBlock_tendstoUniformlyOn F hF).tendsto_at hx

end

end Fabius
