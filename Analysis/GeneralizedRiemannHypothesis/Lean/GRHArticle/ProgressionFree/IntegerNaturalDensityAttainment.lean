import GRHArticle.ProgressionFree.IntegerLargestPrimeBandSelection
import GRHArticle.ProgressionFree.IntegerNearOptimalTemplates
import GRHArticle.ProgressionFree.IntegerTemplateSmoothIndependence
import GRHArticle.ProgressionFree.IntegerLogarithmicDensity

/-!
# Attainment of the integer natural-density supremum

For either ratio convention a single admissible set has natural density
equal to the supremum. Its logarithmic density is the same value.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology

/-- The existence assertion of article theorem `gpi:thm:attain` for both
rational and integral ratios. -/
theorem integerNaturalDensitySupremum_attained (integral : Bool) :
    ∃ B : Set ℕ, 0 ∉ B ∧ IntegerPrefixAdmissible integral B ∧
      HasNaturalDensity B (integerNaturalDensitySupremum integral) := by
  obtain ⟨Y,A,e,hA,he⟩ := exists_integerNearOptimalFiniteTemplates integral
  let E (j : ℕ) := integerRoughTemplateProducts (integerSquarefreeRoughNumbers (Y j)) (A j)
  obtain ⟨M,hM,h0,hYM,hpaste⟩ := exists_integerLargestPrimeBands_of_smooth_independence Y E he
    (fun j ε hε ↦ by
      obtain ⟨K,hK⟩ := hasUniformSmoothDensity_integerRoughTemplateProducts
        (hA j).1 (hA j).2.2 ε hε
      exact ⟨K, fun N Z hN hZ ↦ (hK N Z hN hZ).le⟩)
  exact ⟨integerLargestPrimeBandPaste M E, zero_notMem_integerLargestPrimeBandPaste hM.monotone h0 E,
    integerLargestPrimeBandPaste_template_admissible hM.monotone h0 hYM
      (fun j ↦ (hA j).2.1) (fun j ↦ (hA j).1), hpaste⟩

/-- A common maximizer for natural and upper logarithmic density, with
convergence of its logarithmic densities. -/
theorem exists_integerNatural_and_logDensity_maximizer (integral : Bool) :
    ∃ B : Set ℕ, 0 ∉ B ∧ IntegerPrefixAdmissible integral B ∧
      HasNaturalDensity B (integerNaturalDensitySupremum integral) ∧
      Tendsto (integerLogDensityUpTo B) atTop (𝓝 (integerUpperLogDensitySupremum integral)) := by
  obtain ⟨B,h0,hB,hd⟩ := integerNaturalDensitySupremum_attained integral
  refine ⟨B,h0,hB,hd,?_⟩
  rw [integerUpperLogDensitySupremum_eq_naturalDensitySupremum]
  exact tendsto_integerLogDensityUpTo_of_naturalDensity hd

end GRHArticle.ProgressionFree
