import OAI.Combinatorics.Progressions.Dynamics.PrecenterNativeSelectionBudget
import OAI.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

theorem exists_uniformResidualGood
    {Ω Branch : Type*} [Fintype Ω] [Fintype Branch]
    (law : FiniteProbabilityWeights Ω) (H : Finset Ω)
    (error : Branch → Ω → ℝ) {ε δ : ℝ}
    (herror : ∀ b a, 0 ≤ error b a) (hmean : ∀ b, law.mean (error b) ≤ ε)
    (hH : 0 < law.mass H) (hδ : 0 < δ)
    (hbudget : (Fintype.card Branch : ℝ) * ε ≤ δ * law.mass H / 2) :
    ∃ K : Finset Ω, K ⊆ H ∧ law.mass H / 2 ≤ law.mass K ∧
      0 < law.mass K ∧ ∀ a ∈ K, ∀ b, error b a ≤ δ := by
  classical
  let good := fun a => ∀ b, error b a ≤ δ
  let K := H.filter good
  let B := H.filter (fun a => ¬ good a)
  have htotal (a : Ω) : 0 ≤ ∑ b, error b a := Finset.sum_nonneg (fun b _ => herror b a)
  have hbad (a : Ω) (ha : a ∈ B) : δ ≤ ∑ b, error b a := by
    have hnot : ¬ ∀ b, error b a ≤ δ := (Finset.mem_filter.mp ha).2
    obtain ⟨b, hb⟩ := not_forall.mp hnot
    exact (le_of_not_ge hb).trans
      (Finset.single_le_sum (fun j _ => herror j a) (Finset.mem_univ b))
  have hmeanSum : law.mean (fun a => ∑ b, error b a) ≤
      (Fintype.card Branch : ℝ) * ε := by
    calc
      _ = ∑ b, law.mean (error b) := by
        simp only [mean, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ _b : Branch, ε := Finset.sum_le_sum (fun b _ => hmean b)
      _ = _ := by simp
  have hbadmass : δ * law.mass B ≤ (Fintype.card Branch : ℝ) * ε := by
    calc
      _ = ∑ a ∈ B, law.weight a * δ := by
        simp only [mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ ∑ a ∈ B, law.weight a * ∑ b, error b a :=
        Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hbad a ha) (law.nonneg a))
      _ ≤ law.mean (fun a => ∑ b, error b a) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
          (fun a _ _ => mul_nonneg (law.nonneg a) (htotal a))
      _ ≤ _ := hmeanSum
  have hsplit : law.mass K + law.mass B = law.mass H := by
    exact Finset.sum_filter_add_sum_filter_not H good law.weight
  have hhalf : law.mass H / 2 ≤ law.mass K := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    have hsplitδ := congrArg (fun t : ℝ => δ * t) hsplit
    nlinarith only [hbadmass, hbudget, hsplitδ]
  exact ⟨K, Finset.filter_subset good H, hhalf, (by positivity : 0 < law.mass H / 2).trans_le hhalf,
    fun a ha => (Finset.mem_filter.mp ha).2⟩

theorem uniformResidualGood_exp_budget {Branch : Type*} [Fintype Branch]
    {mass massLog branchLog Eres u : ℝ}
    (hmass : Real.exp (-massLog) ≤ mass)
    (hcard : (Fintype.card Branch : ℝ) ≤ Real.exp branchLog)
    (hu : branchLog + Eres + massLog + 2 ≤ u) :
    (Fintype.card Branch : ℝ) * Real.exp (-u) ≤ Real.exp (-Eres) * mass / 2 := by
  calc
    _ ≤ Real.exp branchLog * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = Real.exp (branchLog - u) := by rw [← Real.exp_add]; rfl
    _ ≤ Real.exp (-(Eres + massLog + 2)) := Real.exp_le_exp.mpr (by linarith only [hu])
    _ ≤ Real.exp (-(Eres + massLog)) / 2 := by
      simpa using VectorPolynomial.precenter_native_selection_model_error_budget 0 (Eres + massLog)
    _ = Real.exp (-Eres) * Real.exp (-massLog) / 2 := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)) (by norm_num)

theorem exists_uniformSliceResidualGood
    {Ω Branch T X : Type*} [Fintype Ω] [Fintype Branch] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (law : FiniteProbabilityWeights Ω) (H : Finset Ω)
    (physical : Ω → T → X) (slices : ∀ a, J a → Finset T)
    (tests : ∀ a, J a → T → ℂ) (signal : Branch → X → ℂ)
    {size ε δ : ℝ} (hS : ∀ a j, (slices a j).Nonempty)
    (hsize : ∀ a j, (Fintype.card T : ℝ) / (slices a j).card ≤ size)
    (htests : ∀ a j t, ‖tests a j t‖ ≤ 1)
    (hmean : ∀ b, sampledSliceSeminorm law physical slices tests (signal b) ≤ ε)
    (hH : 0 < law.mass H) (hδ : 0 < δ)
    (hbudget : (Fintype.card Branch : ℝ) * ε ≤ δ * law.mass H / 2) :
    ∃ K : Finset Ω, K ⊆ H ∧ law.mass H / 2 ≤ law.mass K ∧
      0 < law.mass K ∧ ∀ a ∈ K, ∀ b (j : J a),
        ‖𝔼 t ∈ slices a j, signal b (physical a t) * tests a j t‖ ≤ δ := by
  obtain ⟨K, hKH, hmass, hpos, hgood⟩ := law.exists_uniformResidualGood H
    (fun b => centeredFiniteSliceResidualEnvelope physical slices tests (signal b))
    (fun b => centeredFiniteSliceResidualEnvelope_nonneg physical slices tests (signal b))
    hmean hH hδ hbudget
  refine ⟨K, hKH, hmass, hpos, ?_⟩
  intro a ha b j
  exact (centeredFiniteSliceResidualEnvelope_dominates physical slices tests hS hsize htests
    (signal b) a j).trans (hgood a ha b)

end Erdos3.FiniteProbabilityWeights

end

end OAI
