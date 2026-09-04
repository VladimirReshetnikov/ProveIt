import FabiusFunction.GeometricUniformCDF
import Mathlib.Probability.IdentDistrib

/-!
# Arbitrary-space realizations of geometric uniform laws

The canonical geometric-uniform law is constructed on the countable product
of unit intervals.  This file transfers that construction to an arbitrary
probability space carrying independent uniform coordinates.  It also records
the pointwise convergence and interval bounds of the resulting random series,
so the transfer is about the actual series on the ambient space rather than
only an abstract equality of measures.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators unitInterval

namespace Fabius
namespace ProbabilityRepresentation

set_option autoImplicit false
noncomputable section

/-- The geometric uniform series realized by unit-interval-valued coordinates
on an arbitrary sample space. -/
noncomputable def geometricUniformRealization
    {Ω : Type*} (q : ℝ) (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (ω : Ω) : ℝ :=
  geometricUniformSeries q (fun n => U n ω)

/-- The ambient realization is literally the expected geometric random
series, with no almost-everywhere modification. -/
theorem geometricUniformRealization_eq_tsum
    {Ω : Type*} (q : ℝ) (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (ω : Ω) :
    geometricUniformRealization q U ω =
      ∑' n : ℕ, (1 - q) * q ^ n * (U n ω : ℝ) := by
  unfold geometricUniformRealization geometricUniformSeries
  unfold weightedUniformSeries geometricUniformWeight
  apply tsum_congr
  intro n
  simp only [smul_eq_mul]
  ring

/-- Splitting off the first ambient coordinate gives the geometric affine
recursion pointwise. -/
theorem geometricUniformRealization_split
    {Ω : Type*} {q : ℝ} (hq : |q| < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (ω : Ω) :
    geometricUniformRealization q U ω =
      (1 - q) * (U 0 ω : ℝ) +
        q * geometricUniformRealization q (fun n => U (Nat.succ n)) ω := by
  exact geometricUniformSeries_split hq (fun n => U n ω)

/-- Independent coordinates with the uniform marginal law have the canonical
countable product law. -/
theorem uniformProcess_hasLaw_uniformProduct
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) :
    HasLaw (fun ω n => U n ω) uniformProduct P := by
  simpa only [uniformProduct] using
    hInd.hasLaw_infinitePi hU
      (aemeasurable_pi_iff.2 fun n => (hU n).aemeasurable)

/-- Any absolutely summable weighted uniform series can be realized on an
arbitrary space carrying independent uniform coordinates. -/
theorem weightedUniformSeries_hasLaw_of_iIndep_uniform
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} (w : ℕ → E)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hw : Summable fun n => ‖w n‖)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) :
    HasLaw (fun ω => weightedUniformSeries w (fun n => U n ω))
      (weightedUniformDistribution w) P := by
  have hcoordinates := uniformProcess_hasLaw_uniformProduct U hU hInd
  have hcanonical :
      HasLaw (weightedUniformSeries w) (weightedUniformDistribution w)
        uniformProduct := by
    refine ⟨(measurable_weightedUniformSeries hw).aemeasurable, ?_⟩
    rfl
  simpa only [Function.comp_def] using hcanonical.comp hcoordinates

/-- The geometric series formed from arbitrary independent uniform
coordinates has the canonical geometric-uniform law. -/
theorem geometricUniformRealization_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq : |q| < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) :
    HasLaw (geometricUniformRealization q U)
      (geometricUniformDistribution q) P := by
  change HasLaw
    (fun ω => weightedUniformSeries (geometricUniformWeight q) (fun n => U n ω))
    (weightedUniformDistribution (geometricUniformWeight q)) P
  exact
    weightedUniformSeries_hasLaw_of_iIndep_uniform
      (geometricUniformWeight q) U
      (summable_norm_geometricUniformWeight hq) hU hInd

/-- The defining geometric series converges absolutely for every outcome,
not merely almost everywhere. -/
theorem summable_norm_geometricUniformRealization_terms
    {Ω : Type*} {q : ℝ} (hq : |q| < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (ω : Ω) :
    Summable fun n : ℕ => ‖(1 - q) * q ^ n * (U n ω : ℝ)‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_norm_geometricUniformWeight hq)
  have hu : ‖(U n ω : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (U n ω).property.1]
    exact (U n ω).property.2
  calc
    ‖(1 - q) * q ^ n * (U n ω : ℝ)‖ =
        ‖geometricUniformWeight q n‖ * ‖(U n ω : ℝ)‖ := by
      simp only [geometricUniformWeight, norm_mul]
    _ ≤ ‖geometricUniformWeight q n‖ * 1 :=
      mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ = ‖geometricUniformWeight q n‖ := mul_one _

/-- On the probability range, every value of an ambient geometric-uniform
realization lies in the unit interval. -/
theorem geometricUniformRealization_mem_Icc
    {Ω : Type*} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (ω : Ω) :
    geometricUniformRealization q U ω ∈ Set.Icc (0 : ℝ) 1 := by
  exact geometricUniformSeries_mem_Icc hq0 hq1 (fun n => U n ω)

/-- The pushforward of any independent-uniform realization has exact
topological support `[0,1]`. -/
theorem map_geometricUniformRealization_support_eq_Icc
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) :
    (P.map (geometricUniformRealization q U)).support =
      Set.Icc (0 : ℝ) 1 := by
  have hq : |q| < 1 := by simpa only [abs_of_nonneg hq0] using hq1
  rw [(geometricUniformRealization_hasLaw hq U hU hInd).map_eq]
  exact geometricUniformDistribution_support_eq_Icc hq0 hq1

/-- Every arbitrary-space realization has expectation `1 / 2`. -/
theorem integral_geometricUniformRealization_eq_one_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq : |q| < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) :
    (∫ ω, geometricUniformRealization q U ω ∂P) = 1 / 2 := by
  calc
    (∫ ω, geometricUniformRealization q U ω ∂P) =
        ∫ x : ℝ, x ∂geometricUniformDistribution q :=
      (geometricUniformRealization_hasLaw hq U hU hInd).integral_eq
    _ = 1 / 2 := integral_id_geometricUniformDistribution_eq_one_half hq

/-- Reflection about `1 / 2` preserves the law of every arbitrary-space
geometric-uniform realization. -/
theorem one_sub_geometricUniformRealization_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq : |q| < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) :
    HasLaw (fun ω => 1 - geometricUniformRealization q U ω)
      (geometricUniformDistribution q) P := by
  have hreflect : HasLaw (fun x : ℝ => 1 - x)
      (geometricUniformDistribution q) (geometricUniformDistribution q) := by
    refine ⟨(by fun_prop), ?_⟩
    exact geometricUniformDistribution_reflection hq
  simpa only [Function.comp_def] using
    hreflect.comp (geometricUniformRealization_hasLaw hq U hU hInd)

/-- An arbitrary-space geometric realization and its reflection are
identically distributed. -/
theorem geometricUniformRealization_identDistrib_one_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq : |q| < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) :
    IdentDistrib (geometricUniformRealization q U)
      (fun ω => 1 - geometricUniformRealization q U ω) P P :=
  (geometricUniformRealization_hasLaw hq U hU hInd).identDistrib
    (one_sub_geometricUniformRealization_hasLaw hq U hU hInd)

/-- A fresh uniform coordinate and an independent copy of the geometric law
satisfy the affine fixed-point identity in distribution. -/
theorem affine_uniform_geometric_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {q : ℝ} (hq : |q| < 1)
    (V : Ω → Set.Icc (0 : ℝ) 1) (Y : Ω → ℝ)
    (hV : HasLaw V (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hY : HasLaw Y (geometricUniformDistribution q) P)
    (hInd : IndepFun V Y P) :
    HasLaw (fun ω => (1 - q) * (V ω : ℝ) + q * Y ω)
      (geometricUniformDistribution q) P := by
  have hpair := hInd.hasLaw_prod hV hY
  have haffine : HasLaw
      (fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
        (1 - q) * (p.1 : ℝ) + q * p.2)
      (geometricUniformDistribution q)
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (geometricUniformDistribution q)) := by
    refine ⟨(by fun_prop), ?_⟩
    exact (geometricUniformDistribution_selfSimilar hq).symm
  simpa only [Function.comp_def] using haffine.comp hpair

/-- Splitting against a fresh independent copy gives the manuscript's
affine fixed-point identity in distribution on an arbitrary sample space. -/
theorem geometricUniformRealization_identDistrib_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {q : ℝ} (hq : |q| < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (Y : Ω → ℝ)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hCoords : iIndepFun U P)
    (hY : HasLaw Y (geometricUniformDistribution q) P)
    (hInd : IndepFun (U 0) Y P) :
    IdentDistrib (geometricUniformRealization q U)
      (fun ω => (1 - q) * (U 0 ω : ℝ) + q * Y ω) P P :=
  (geometricUniformRealization_hasLaw hq U hU hCoords).identDistrib
    (affine_uniform_geometric_hasLaw hq (U 0) Y (hU 0) hY hInd)

/-- The distribution function of any arbitrary-space realization is the
canonical geometric-uniform CDF. -/
theorem measureReal_geometricUniformRealization_le_eq_cdf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq : |q| < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) (x : ℝ) :
    P.real {ω | geometricUniformRealization q U ω ≤ x} =
      geometricUniformCDF q x := by
  letI : IsProbabilityMeasure (geometricUniformDistribution q) :=
    geometricUniformDistribution_isProbabilityMeasure hq
  rw [geometricUniformCDF, ProbabilityTheory.cdf_eq_real]
  exact (geometricUniformRealization_hasLaw hq U hU hInd).measureReal_eq
    measurableSet_Iic

/-- The CDF of an arbitrary realization obeys the conditioning/refinement
equation from the independent-copy decomposition. -/
theorem measureReal_geometricUniformRealization_le_eq_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) (x : ℝ) :
    P.real {ω | geometricUniformRealization q U ω ≤ x} =
      ∫ u : Set.Icc (0 : ℝ) 1,
        P.real {ω | geometricUniformRealization q U ω ≤
          (x - (1 - q) * (u : ℝ)) / q} := by
  have hq : |q| < 1 := by simpa only [abs_of_pos hq0] using hq1
  calc
    P.real {ω | geometricUniformRealization q U ω ≤ x} =
        geometricUniformCDF q x :=
      measureReal_geometricUniformRealization_le_eq_cdf hq U hU hInd x
    _ = ∫ u : Set.Icc (0 : ℝ) 1,
        geometricUniformCDF q ((x - (1 - q) * (u : ℝ)) / q) :=
      geometricUniformCDF_eq_integral hq0 hq1 x
    _ = ∫ u : Set.Icc (0 : ℝ) 1,
        P.real {ω | geometricUniformRealization q U ω ≤
          (x - (1 - q) * (u : ℝ)) / q} := by
      apply integral_congr_ae
      filter_upwards with u
      symm
      exact measureReal_geometricUniformRealization_le_eq_cdf hq U hU hInd _

/-- The realization CDF vanishes on the nonpositive half-line. -/
theorem measureReal_geometricUniformRealization_le_eq_zero_of_nonpos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) {x : ℝ} (hx : x ≤ 0) :
    P.real {ω | geometricUniformRealization q U ω ≤ x} = 0 := by
  have hq : |q| < 1 := by simpa only [abs_of_nonneg hq0] using hq1
  rw [measureReal_geometricUniformRealization_le_eq_cdf hq U hU hInd]
  exact geometricUniformCDF_zero_of_nonpos hq0 hq1 hx

/-- The realization CDF is one on the half-line starting at one. -/
theorem measureReal_geometricUniformRealization_le_eq_one_of_one_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1)
    (hU : ∀ n, HasLaw (U n)
      (volume : Measure (Set.Icc (0 : ℝ) 1)) P)
    (hInd : iIndepFun U P) {x : ℝ} (hx : 1 ≤ x) :
    P.real {ω | geometricUniformRealization q U ω ≤ x} = 1 := by
  have hq : |q| < 1 := by simpa only [abs_of_nonneg hq0] using hq1
  rw [measureReal_geometricUniformRealization_le_eq_cdf hq U hU hInd]
  exact geometricUniformCDF_one_of_one_le hq0 hq1 hx

end

end ProbabilityRepresentation
end Fabius
