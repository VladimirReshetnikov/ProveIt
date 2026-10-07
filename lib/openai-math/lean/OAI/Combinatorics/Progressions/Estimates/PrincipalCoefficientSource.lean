import Mathlib.Probability.Independence.Basic

namespace OAI

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

theorem finiteProductMarginal_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (e : J → I) (he : Function.Injective e) :
    MeasurePreserving (fun x : I → X => fun j => x (e j))
      (Measure.pi μ) (Measure.pi (fun j => μ (e j))) := by
  have hind : iIndepFun (fun i (x : I → X) => x i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hsel := iIndepFun.precomp he hind
  have hm := hsel.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  refine ⟨by fun_prop, hm.trans ?_⟩
  congr 1
  funext j
  exact (measurePreserving_eval μ (e j)).map_eq

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteProduct_coordinates_ae {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (P : I → X → Prop)
    (hP : ∀ i, ∀ᵐ x ∂μ i, P i x) : ∀ᵐ x ∂Measure.pi μ, ∀ i, P i (x i) :=
  Filter.eventually_all.mpr (fun i => (measurePreserving_eval μ i).quasiMeasurePreserving.ae (hP i))

noncomputable def principalCoefficientBudget {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (C : D → ℝ) : ℝ :=
  ∑ d, (Fintype.card (B d) : ℝ) * C d

theorem principalCoefficientBudget_nonneg {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] {C : D → ℝ} (hC : ∀ d, 0 ≤ C d) :
    0 ≤ principalCoefficientBudget B C :=
  Finset.sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg _) (hC d))

theorem principalCoefficientBudget_axis_le {D : Type*} [Fintype D]
    {B : D → Type*} [∀ d, Fintype (B d)] (c : ∀ d, B d → ℝ) {C : D → ℝ}
    (hC : ∀ d, 0 ≤ C d) (hc : ∀ d b, |c d b| ≤ C d) (d : D) :
    (∑ b, |c d b|) ≤ principalCoefficientBudget B C := by
  classical
  calc
    _ ≤ ∑ _b : B d, C d := Finset.sum_le_sum (fun b _ => hc d b)
    _ = (Fintype.card (B d) : ℝ) * C d := by simp
    _ ≤ _ := Finset.single_le_sum
      (fun e _ => mul_nonneg (Nat.cast_nonneg (Fintype.card (B e))) (hC e)) (Finset.mem_univ d)

theorem independentPrincipalSource_bounds {D Z : Type*} [Fintype D] [Fintype Z]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (μ : (Σ d, B d) → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure (Z → ℝ)) [IsProbabilityMeasure ν]
    (c₀ C : D → ℝ) (hC : ∀ d, 0 ≤ C d)
    (hμ : ∀ i, ∀ᵐ u ∂μ i, c₀ i.1 ≤ |u| ∧ |u| ≤ C i.1)
    (hν : ∀ᵐ z ∂ν, ∀ j, |z j| ≤ 1) :
    ∀ᵐ p ∂(Measure.pi μ).prod ν,
      (∀ j, |p.2 j| ≤ 1) ∧ (∀ d b, c₀ d ≤ |p.1 ⟨d, b⟩| ∧ |p.1 ⟨d, b⟩| ≤ C d) ∧
      (∀ d, (∑ b, |p.1 ⟨d, b⟩|) ≤ principalCoefficientBudget B C) := by
  have hpi := finiteProduct_coordinates_ae μ (fun i u => c₀ i.1 ≤ |u| ∧ |u| ≤ C i.1) hμ
  have hl := (measurePreserving_fst (μ := Measure.pi μ) (ν := ν)).quasiMeasurePreserving.ae hpi
  have hr := (measurePreserving_snd (μ := Measure.pi μ) (ν := ν)).quasiMeasurePreserving.ae hν
  filter_upwards [hl, hr] with p hp hq
  refine ⟨hq, (fun d b => hp ⟨d, b⟩), ?_⟩
  exact principalCoefficientBudget_axis_le (fun d b => p.1 ⟨d, b⟩) hC (fun d b => (hp ⟨d, b⟩).2)

end Erdos3

end

end OAI
