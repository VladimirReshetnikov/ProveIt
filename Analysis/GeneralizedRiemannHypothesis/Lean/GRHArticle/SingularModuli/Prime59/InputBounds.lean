import GRHArticle.SingularModuli.Prime59.InputPrefixes

namespace GRHArticle.SingularModuli.Prime59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem invariant_nonnegative : ∀ a ∈ invariant, 0 ≤ a := by
  have h : invariant.all (fun a ↦ decide (0 ≤ a)) = true := by decide +kernel
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp h a ha)

theorem invariantNatural_map : invariantNatural.map Int.ofNat = invariant := by
  rw [invariantNatural, List.map_map]
  calc
    invariant.map (Int.ofNat ∘ Int.toNat) = invariant.map id :=
      List.map_congr_left (fun a ha ↦ Int.toNat_of_nonneg (invariant_nonnegative a ha))
    _ = invariant := List.map_id _

theorem invariant_dyadic_bound :
    dyadicScaledEvaluation invariantNatural ≤ 2^(invariantNatural.length+dyadicExponent) := by
  decide +kernel

end GRHArticle.SingularModuli.Prime59
