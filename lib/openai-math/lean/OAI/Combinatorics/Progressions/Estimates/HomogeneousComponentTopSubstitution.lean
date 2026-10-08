/- Modified for ProveIt: use MvPolynomial.coeff_zero in the top-component
substitution proof on Lean 4.32. The upstream theorem statement is unchanged. -/
import OAI.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem weightedTop_aeval (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : MvPolynomial σ R) (n : ℕ) (hp : p ∈ weightedSupportLE w n) :
    weightedHomogeneousComponent v n (aeval β p) =
      aeval (fun i => weightedHomogeneousComponent v (w i) (β i))
        (weightedHomogeneousComponent w n p) := by
  classical
  let top : σ → MvPolynomial τ R :=
    fun i => weightedHomogeneousComponent v (w i) (β i)
  have hdiff : aeval β p - aeval top p ∈ weightedSupportLT v n := by
    apply weightedComparison_difference w v (aeval β) (aeval top) _ _ _ hp
    · intro i
      simpa only [aeval_X] using hβ i
    · intro i
      simpa only [aeval_X, top] using weightedTopPart_preserves_degree v v (w i) (hβ i)
    · intro i
      simpa only [aeval_X, top] using weightedTopPart_remainder_lt v (hβ i)
  have hzero : weightedHomogeneousComponent v n (aeval β p - aeval top p) = 0 := by
    ext α
    rw [coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
    split_ifs with hα
    · by_contra hc
      have hlt := hdiff (mem_support_iff.mpr hc)
      change Finsupp.weight v α < n at hlt
      omega
    · rfl
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero.trans (aeval_weightedHomogeneousComponent w v top
    (fun i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) n p).symm

end Erdos3

end

end OAI
