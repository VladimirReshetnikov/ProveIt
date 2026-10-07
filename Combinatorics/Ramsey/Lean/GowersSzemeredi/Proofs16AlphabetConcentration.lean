import Mathlib.Probability.Moments.SubGaussian

/-! Exponential concentration for finite sums of independent bounded
variables. This supplies the probabilistic estimate for balanced alphabet
words on a finite family of progressions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace LeanProofs.GowersSzemeredi

theorem finiteAlphabet_hoeffding {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → Real)
    (hindep : iIndepFun X μ) (hm : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : Real) 1)
    (T : Finset I) (p epsilon : Real) (hε : 0 ≤ epsilon)
    (hmean : ∀ i ∈ T, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (p + epsilon) * T.card ≤ ∑ i ∈ T, X i ω} ≤
      Real.exp (-2 * epsilon ^ 2 * T.card) := by
  have hc : iIndepFun (fun i ω => X i ω - p) μ :=
    hindep.comp (fun _ x => x - p) (fun _ => by fun_prop)
  have hsg (i : I) (hi : i ∈ T) :
      HasSubgaussianMGF (fun ω => X i ω - p) (1 / 4 : NNReal) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
    rw [hmean i hi] at h
    convert h using 1 <;> norm_num
  have ht := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hc hsg
    (mul_nonneg hε (Nat.cast_nonneg T.card))
  have he : {ω | epsilon * (T.card : Real) ≤ ∑ i ∈ T, (X i ω - p)} =
      {ω | (p + epsilon) * T.card ≤ ∑ i ∈ T, X i ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    constructor <;> intro h <;> nlinarith only [h]
  rw [he] at ht
  have hpow : -(epsilon * (T.card : Real)) ^ 2 / (2 * ∑ _i ∈ T, ((1 / 4 : NNReal) : Real)) =
      -2 * epsilon ^ 2 * T.card := by
    simp only [Finset.sum_const, nsmul_eq_mul, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    by_cases hz : T.card = 0
    · simp [hz]
    · have hn : (T.card : Real) ≠ 0 := by exact_mod_cast hz
      field_simp
      <;> ring
  simpa only [NNReal.coe_sum, hpow] using ht

end LeanProofs.GowersSzemeredi
