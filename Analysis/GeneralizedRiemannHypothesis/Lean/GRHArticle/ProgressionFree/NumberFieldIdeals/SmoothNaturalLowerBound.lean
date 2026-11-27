import GRHArticle.ProgressionFree.NumberFieldIdeals.SquarefreeExterior
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothOptimization

/-!
# Extending the smooth natural-density optimization to all ideals

Every admissible smooth template extends via the squarefree exterior.
Taking the supremum gives the lower estimate for the natural-density
extremum even if no maximizing template has been chosen.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The comparison `vB ≤ b_K` for any finite set of prime ideals. -/
theorem squarefree_mul_smoothLower_le_idealNaturalDensitySupremum (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    idealSquarefreeExteriorFactor S * idealSmoothLowerOptimization integral S ≤
      idealNaturalDensitySupremum K integral := by
  let v := idealSquarefreeExteriorFactor S
  let c := idealSmoothDensityFactor S
  have hvc : 0 < v*c := mul_pos (idealSquarefreeExteriorFactor_pos S) (idealSmoothDensityFactor_pos S)
  change v * (c * sSup _) ≤ _
  rw [← mul_assoc, mul_comm (v*c), ← le_div_iff₀ hvc]
  apply csSup_le
  · exact ⟨_, ∅, Set.empty_subset _, fun _ _ _ ha ↦ ha.elim, rfl⟩
  · rintro _ ⟨F,hF,hA,rfl⟩
    apply (le_div_iff₀ hvc).mpr
    calc
      _ = c * idealReciprocalWeight (K := K) F * v := by ring
      _ ≤ _ := squarefreeExterior_mul_weight_le_supremum S integral F hF hA

end GRHArticle.ProgressionFree.NumberFieldIdeals
