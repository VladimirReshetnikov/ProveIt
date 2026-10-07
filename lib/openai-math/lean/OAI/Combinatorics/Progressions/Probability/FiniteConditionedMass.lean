-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.MeasureTheory.Measure.Real
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest
import OAI.Compat.Core

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteProbabilityWeights Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

theorem uniform_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).mean f = 𝔼 x, f x := by
  simp only [mean, uniform, ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

theorem uniform_complexMean {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℂ) :
    (uniform Ω).complexMean f = 𝔼 x, f x := by
  simp only [complexMean, uniform, Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

theorem uniform_correlation {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f g : Ω → ℂ) :
    (uniform Ω).correlation f g = 𝔼 x, f x * star (g x) :=
  uniform_complexMean _

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def eventProbability {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : ℝ := by
  classical
  exact p.mean (fun x => if E x then 1 else 0)

theorem eventProbability_nonneg {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : 0 ≤ p.eventProbability E := by
  classical
  exact p.mean_nonneg (fun x => by split_ifs <;> norm_num)

theorem eventProbability_false {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) (hE : ∀ x, ¬ E x) : p.eventProbability E = 0 := by
  classical
  simp only [eventProbability, hE, ite_false]
  exact p.mean_const 0

theorem eventProbability_mono {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E F : Ω → Prop) (hEF : ∀ x, E x → F x) : p.eventProbability E ≤ p.eventProbability F := by
  classical
  apply p.mean_mono
  intro x
  by_cases hE : E x
  · simp [hE, hEF x hE]
  · simp only [hE, ite_false]
    split_ifs <;> norm_num

theorem eventProbability_union_bound {Ω C : Type*} [Fintype Ω] [Fintype C]
    (p : FiniteProbabilityWeights Ω) (E : Ω → Prop) (F : C → Ω → Prop)
    (hEF : ∀ x, E x → ∃ c, F c x) :
    p.eventProbability E ≤ ∑ c, p.eventProbability (F c) := by
  classical
  have hpoint (x) : (if E x then (1 : ℝ) else 0) ≤ ∑ c, if F c x then (1 : ℝ) else 0 := by
    by_cases hE : E x
    · obtain ⟨c, hc⟩ := hEF x hE
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun c => if F c x then (1 : ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ c)
      simpa only [hE, hc, ite_true] using h
    · simp only [hE, ite_false]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  apply (p.mean_mono hpoint).trans_eq
  simp only [eventProbability, mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_pi_product {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v : ∀ j, Ω j → ℝ) :
    (pi p).mean (fun x => ∏ j, v j (x j)) = ∏ j, (p j).mean (v j) := by
  classical
  change (∑ x : ∀ j, Ω j, (∏ j, (p j).weight (x j)) * (∏ j, v j (x j))) =
    ∏ j, ∑ x, (p j).weight x * v j x
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j (x : Ω j) => (p j).weight x * v j x)).symm

theorem eventProbability_pi {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (E : ∀ j, Ω j → Prop) :
    (pi p).eventProbability (fun x => ∀ j, E j (x j)) = ∏ j, (p j).eventProbability (E j) := by
  classical
  have hpoint (x : ∀ j, Ω j) :
      (@ite ℝ (∀ j, E j (x j)) (Classical.propDecidable _) 1 0) =
        ∏ j, if E j (x j) then (1 : ℝ) else 0 := by
    by_cases h : ∀ j, E j (x j)
    · simp [h]
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  simpa only [eventProbability] using
    (congrArg (pi p).mean (funext hpoint)).trans
      (mean_pi_product p (fun j y => if E j y then (1 : ℝ) else 0))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem uniform_mass {Ω : Type*} [Fintype Ω] [Nonempty Ω] (G : Finset Ω) :
    (uniform Ω).mass G = (G.card : ℝ) / Fintype.card Ω := by
  simp [mass, uniform, div_eq_mul_inv]

theorem uniform_condition_weight_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (G : Finset Ω) (hG : 0 < (uniform Ω).mass G) (c : ℝ) (hc : 0 < c)
    (hmass : c ≤ (uniform Ω).mass G) (x : Ω) :
    ((uniform Ω).condition G hG).weight x ≤ c⁻¹ * (Fintype.card Ω : ℝ)⁻¹ := by
  have hcard : (0 : ℝ) ≤ (Fintype.card Ω : ℝ)⁻¹ := by positivity
  change (if x ∈ G then (Fintype.card Ω : ℝ)⁻¹ else 0) / (uniform Ω).mass G ≤ _
  by_cases hx : x ∈ G
  · rw [ite_eq_left hx, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hc hmass) hcard
  · rw [ite_eq_right hx, zero_div]
    positivity

theorem uniform_condition_mean {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (G : Finset Ω) (hG : 0 < (uniform Ω).mass G) (f : Ω → ℝ) :
    ((uniform Ω).condition G hG).mean f = 𝔼 x : G, f x := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hg : (G.card : ℝ) ≠ 0 := by
    intro hz
    rw [uniform_mass, hz, zero_div] at hG
    exact (lt_irrefl _ hG)
  rw [condition_mean, uniform_mean, uniform_mass, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, Finset.sum_coe_sort G f, Fintype.card_coe]
  have hsum : (∑ x, if x ∈ G then f x else 0) = ∑ x ∈ G, f x := by simp
  rw [hsum]
  field_simp

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem condition_eventProbability_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (hG : 0 < p.mass G) (E : Ω → Prop) :
    (p.condition G hG).eventProbability E ≤ p.eventProbability E / p.mass G := by
  classical
  unfold eventProbability
  rw [condition_mean]
  apply div_le_div_of_nonneg_right _ hG.le
  apply p.mean_mono
  intro x
  by_cases hx : x ∈ G <;> by_cases hE : E x <;> simp [hx, hE]

theorem eventProbability_le_of_weight_le {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) (C : ℝ)
    (hw : ∀ x, p.weight x ≤ C * q.weight x) (E : Ω → Prop) :
    p.eventProbability E ≤ C * q.eventProbability E := by
  classical
  unfold eventProbability mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x <;> simp [hx, hw x]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem disjoint_cells_card_mul_le {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (μ : Measure X) (C : Ω → Set X) (A : Set X) (v : ℝ)
    (hdis : Pairwise (fun a b => Disjoint (C a) (C b))) (hm : ∀ ω, MeasurableSet (C ω))
    (hfin : ∀ ω, μ (C ω) ≠ ⊤) (hv : ∀ ω, μ.real (C ω) = v)
    (hsub : ∀ ω, C ω ⊆ A) (hA : μ A ≠ ⊤) :
    (Fintype.card Ω : ℝ) * v ≤ μ.real A := by
  have heq : μ.real (⋃ ω, C ω) = (Fintype.card Ω : ℝ) * v := by
    rw [measureReal_iUnion_fintype hdis hm hfin]
    simp only [hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← heq]
  exact measureReal_mono (Set.iUnion_subset hsub) hA

theorem finite_cell_event_probability_le {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (p : FiniteProbabilityWeights Ω) (E : Ω → Prop)
    (μ : Measure X) (C : Ω → Set X) (A : Set X) (M v : ℝ) (hM : 0 ≤ M)
    (hdis : Pairwise (fun a b => Disjoint (C a) (C b))) (hm : ∀ ω, MeasurableSet (C ω))
    (hfin : ∀ ω, μ (C ω) ≠ ⊤) (hv : ∀ ω, μ.real (C ω) = v)
    (hw : ∀ ω, p.weight ω ≤ M * v) (hsub : ∀ ω, E ω → C ω ⊆ A) (hA : μ A ≠ ⊤) :
    p.eventProbability E ≤ M * μ.real A := by
  classical
  let S := Finset.univ.filter E
  have hc : (S.card : ℝ) * v ≤ μ.real A := by
    have h := disjoint_cells_card_mul_le μ (fun ω : S => C ω.val) A v
      (fun a b hab => hdis (Subtype.coe_injective.ne hab))
      (fun ω => hm ω) (fun ω => hfin ω) (fun ω => hv ω)
      (fun ω => hsub ω (Finset.mem_filter.mp ω.property).2) hA
    simpa only [Fintype.card_coe] using h
  calc
    p.eventProbability E = ∑ ω ∈ S, p.weight ω := by
      simp only [FiniteProbabilityWeights.eventProbability, FiniteProbabilityWeights.mean,
        S, Finset.sum_filter, mul_ite, mul_one, mul_zero]
    _ ≤ ∑ _ω ∈ S, M * v := Finset.sum_le_sum (fun ω _ => hw ω)
    _ = M * ((S.card : ℝ) * v) := by simp [mul_left_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hM

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem condition_mass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G) :
    (p.condition G hG).mass R = p.mass (G ∩ R) / p.mass G := by
  simp only [mass, condition]
  rw [← Finset.sum_div, ← Finset.sum_filter]
  congr 1
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, and_comm]

theorem mass_inter_le_condition_mass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G) :
    p.mass (G ∩ R) ≤ (p.condition G hG).mass R := by
  rw [condition_mass]
  apply (le_div_iff₀ hG).mpr
  exact mul_le_of_le_one_right (p.mass_nonneg _) (p.mass_le_one G)

theorem condition_weight_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (hG : 0 < p.mass G)
    (c : ℝ) (hc : 0 < c) (hmass : c ≤ p.mass G) (x : Ω) :
    (p.condition G hG).weight x ≤ c⁻¹ * p.weight x := by
  change (if x ∈ G then p.weight x else 0) / p.mass G ≤ _
  by_cases hx : x ∈ G
  · rw [ite_eq_left hx, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hc hmass) (p.nonneg x)
  · rw [ite_eq_right hx, zero_div]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (p.nonneg x)

end Erdos3.FiniteProbabilityWeights

end

end OAI
