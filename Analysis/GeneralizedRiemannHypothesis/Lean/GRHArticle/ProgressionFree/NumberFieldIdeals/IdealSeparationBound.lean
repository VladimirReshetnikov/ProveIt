import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealUpperDensityLower
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothNaturalUpperBound
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothOptimizationGap

/-!
# The quantitative density separation bound for ideals

Combine the positive finite smooth obstruction with the global upper and
natural density comparisons. The loss from exterior prime squares has
an explicit field-degree bound.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter

variable {K : Type*} [Field K] [NumberField K]

theorem idealSquarefreeExteriorFactor_le_one (S : Finset (HeightOneSpectrum (𝓞 K))) :
    idealSquarefreeExteriorFactor S ≤ 1 := by
  have h := (exteriorRuleProduct_pos S (fun _ ↦ ({0,1} : Set ℕ)) (by simp)).1.hasProd
  have he : (∏' p : {p // p ∉ S}, localRuleMass p.val ({0,1} : Set ℕ)) ≤ 1 := by
    apply le_of_tendsto h
    exact Eventually.of_forall fun s ↦ prod_le_one
      (fun j _ ↦ (localRuleMass_mem_unitInterval j.val _).1)
      (fun j _ ↦ (localRuleMass_mem_unitInterval j.val _).2)
  simpa only [idealSquarefreeExteriorFactor, localRuleMass_zero_one] using he

/-- The same smooth obstruction works with any finite set of primes
containing the designated one, with its exact exterior Euler loss. -/
theorem idealDensitySeparation_at_prime (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) :
    idealSmoothDensityFactor S * integerPrefixStepWeight (absNorm p.val.asIdeal ^ 8) -
      (1 - idealSquarefreeExteriorFactor S) ≤
      idealUpperDensitySupremum K integral - idealNaturalDensitySupremum K integral :=
  idealDensityGap_of_smoothBounds integral S p
    (idealNaturalDensitySupremum_le_smoothLowerOptimization integral S)
    (idealSquarefreeExteriorFactor_mul_smoothUpper_le_upperDensitySupremum integral S)
    (idealSquarefreeExteriorFactor_le_one S) le_rfl

/-- The quantitative inequality in `gpi:eq:ideal-gap` for either ratio
convention, any number field, and every cutoff above the chosen prime norm. -/
theorem idealDensitySeparation_normCutoff (integral : Bool)
    (p : HeightOneSpectrum (𝓞 K)) (Y : ℕ) (hp : absNorm p.asIdeal ≤ Y) :
    idealSmoothDensityFactor (primesThroughNorm K Y) /
      ((absNorm p.asIdeal : ℝ)^8 * ((absNorm p.asIdeal : ℝ)^8+1)) - (Module.finrank ℚ K : ℝ)/Y ≤
      idealUpperDensitySupremum K integral - idealNaturalDensitySupremum K integral := by
  let S := primesThroughNorm K Y
  let q : S := ⟨p,(mem_primesThroughNorm p Y).mpr hp⟩
  have hY := (absNorm_pos_of_nonZeroDivisors (primeIdeal p)).trans_le hp
  have h := idealDensityGap_of_smoothBounds integral S q
    (idealNaturalDensitySupremum_le_smoothLowerOptimization integral S)
    (idealSquarefreeExteriorFactor_mul_smoothUpper_le_upperDensitySupremum integral S)
    (idealSquarefreeExteriorFactor_le_one S) (one_sub_squarefreeExteriorFactor_le_finrank_div Y hY)
  simpa only [q,S,integerPrefixStepWeight,Nat.cast_pow,mul_one_div] using h

end GRHArticle.ProgressionFree.NumberFieldIdeals
