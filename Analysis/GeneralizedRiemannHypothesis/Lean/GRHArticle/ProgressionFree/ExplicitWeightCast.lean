import GRHArticle.ProgressionFree.ExplicitArithmetic
import GRHArticle.ProgressionFree.FourMarkerExchange
import Mathlib.Data.Rat.BigOperators

/-!
# The rational certificate in the real-valued four-marker weight formula
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

noncomputable def explicitSatelliteWeight (p : ↥explicitOddPrimes) : ℝ :=
  1 / (p.val : ℝ)

theorem explicitSatelliteWeight_prod :
    (∏ p : ↥explicitOddPrimes, explicitSatelliteWeight p) = 1 / (explicitOddPrimeProduct : ℝ) := by
  simp only [explicitSatelliteWeight, explicitOddPrimeProduct, Finset.prod_coe_sort, Nat.cast_prod,
    one_div, Finset.prod_inv_distrib]

/-- The real reciprocal-weight gain lower bound is the cast of the exact
rational certificate. -/
theorem explicit_scaledGain_eq_real :
    let m : ℝ := ∑ k ∈ fourMarkerExponents, (1 / (2 : ℝ)) ^ k
    let v : ℝ := ∑ k ∈ fourMarkerExponents, (1 / (2 : ℝ)) ^ (2 * k)
    let U : ℝ := (explicitUpsilon : ℝ)
    m - (U - 1) +
      ∑ i : ↥explicitOddPrimes, (m * explicitSatelliteWeight i - v * explicitSatelliteWeight i ^ 2 -
        (U - m) * explicitSatelliteWeight i ^ 3) = (explicitScaledGain : ℝ) := by
  intro m v U
  have hmarkers : explicitMarkers = fourMarkerExponents := rfl
  have hm : (explicitMarkerMass : ℝ) = m := by
    simp only [m, explicitMarkerMass, hmarkers, Rat.cast_sum, Rat.cast_div, Rat.cast_one,
      Rat.cast_pow, Rat.cast_ofNat, div_pow, one_pow]
  have hv : (explicitDoubleMarkerMass : ℝ) = v := by
    simp only [v, explicitDoubleMarkerMass, hmarkers, Rat.cast_sum, Rat.cast_div, Rat.cast_one,
      Rat.cast_pow, Rat.cast_ofNat, div_pow, one_pow]
  simp only [explicitScaledGain, Rat.cast_add, Rat.cast_sub, Rat.cast_one, Rat.cast_sum, hm]
  apply congrArg (m - (U - 1) + ·)
  let term (p : ℕ) : ℝ := m * (1 / (p : ℝ)) - v * (1 / (p : ℝ)) ^ 2 -
    (U - m) * (1 / (p : ℝ)) ^ 3
  change (∑ i : ↥explicitOddPrimes, term i.val) = _
  rw [Finset.sum_coe_sort explicitOddPrimes term]
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_sub, hm, hv]
  simp only [term, div_eq_mul_inv, one_mul, inv_pow, U]

end GRHArticle.ProgressionFree
