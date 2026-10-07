import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {K Z : Type*} [Countable K] [MeasurableSpace K]
  [MeasurableSingletonClass K] [MeasurableSpace Z]
  (μ : Measure Z) [SFinite μ]

omit [Countable K] in

theorem forecastFiniteSpatialFamily_integrable
    (F : K → Z → ℂ) (s : Finset K)
    (hf : ∀ k ∈ s, Integrable (F k) μ)
    (hzero : ∀ k ∉ s, ∀ z, F k z = 0) :
    Integrable (fun p : K × Z => F p.1 p.2) (Measure.count.prod μ) := by
  classical
  have hi (k : K) : Integrable (fun j : K => if j = k then (1 : ℂ) else 0)
      Measure.count := by
    apply integrable_count_iff.mpr
    apply summable_of_ne_finset_zero (s := {k})
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]
  have hs := integrable_finsetSum s (fun k hk => (hi k).mul_prod (hf k hk))
  have heq : (fun p : K × Z => F p.1 p.2) =
      (fun p : K × Z => ∑ k ∈ s, (if p.1 = k then (1 : ℂ) else 0) * F k p.2) := by
    funext p
    by_cases hp : p.1 ∈ s
    · rw [Finset.sum_eq_single p.1]
      · simp
      · intro b hb hbp
        simp [Ne.symm hbp]
      · exact fun hn => (hn hp).elim
    · rw [hzero p.1 hp p.2]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have hpb : p.1 ≠ b := fun h => hp (h ▸ hb)
      simp [hpb]
  rw [heq]
  exact hs

theorem forecastFiniteSpatialFamily_sum_integral
    (F : K → Z → ℂ) (s : Finset K)
    (hf : ∀ k ∈ s, Integrable (F k) μ)
    (hzero : ∀ k ∉ s, ∀ z, F k z = 0) :
    (∑ k ∈ s, ∫ z, F k z ∂μ) =
      ∫ p : K × Z, F p.1 p.2 ∂(Measure.count.prod μ) := by
  classical
  have hi := forecastFiniteSpatialFamily_integrable μ F s hf hzero
  rw [integral_prod _ hi, integral_countable hi.integral_prod_left]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  symm
  apply tsum_eq_sum
  intro k hk
  simp [hzero k hk]

end Erdos3.VectorPolynomial

end

end OAI
