import FabiusFunction.FabiusLegendreGaunt
import FabiusFunction.LegendreGauntClosedForm

/-!
# Finite Wigner-square sums for the Rvachev Legendre Gram matrix

The finite Gaunt expansions of the executable rational Rvachev Legendre Gram
entries become finite zero-row Wigner-square sums after substituting the exact
Gaunt--Wigner-square identity.  The same substitution gives entry formulas for
the rational Gram matrix and, after casting, for the real up-law Gram matrix.

Only the total squared integer-index zero-row datum defined in
`LegendreGauntClosedForm` occurs here.  No signed Wigner symbol or phase
convention is chosen, and no half-integer, nonzero-magnetic-index, general
`3j`/`6j`/`9j`, orthogonality, recoupling, or infinite-series statement is
claimed.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Fabius

/-! ## Finite rational and real Wigner-square sums -/

/-- Every executable rational Rvachev Legendre Gram entry is twice the finite
sum of the canonical even coefficients against the total rational zero-row
Wigner-square datum. -/
theorem rvachevLegendreGramEntryRat_eq_two_mul_sum_wignerThreeJZeroSqRat
    (i j : ℕ) :
    rvachevLegendreGramEntryRat i j =
      2 * ∑ r ∈ range ((i + j) / 2 + 1),
        canonicalRvachevLegendreCoefficientRat r *
          legendreWignerThreeJZeroSqRat i j (2 * r) := by
  calc
    rvachevLegendreGramEntryRat i j =
        ∑ r ∈ range ((i + j) / 2 + 1),
          canonicalRvachevLegendreCoefficientRat r *
            legendreGauntRat i j (2 * r) :=
      rvachevLegendreGramEntryRat_eq_sum_gaunt i j
    _ = ∑ r ∈ range ((i + j) / 2 + 1),
          canonicalRvachevLegendreCoefficientRat r *
            (2 * legendreWignerThreeJZeroSqRat i j (2 * r)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat]
    _ = 2 * ∑ r ∈ range ((i + j) / 2 + 1),
          canonicalRvachevLegendreCoefficientRat r *
            legendreWignerThreeJZeroSqRat i j (2 * r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

/-- Every entry of the executable rational Rvachev Legendre Gram matrix is
twice its finite canonical-coefficient zero-row Wigner-square sum. -/
theorem rvachevLegendreGramMatrixRat_apply_eq_two_mul_sum_wignerThreeJZeroSqRat
    (n : ℕ) (i j : Fin n) :
    rvachevLegendreGramMatrixRat n i j =
      2 * ∑ r ∈ range (((i : ℕ) + (j : ℕ)) / 2 + 1),
        canonicalRvachevLegendreCoefficientRat r *
          legendreWignerThreeJZeroSqRat (i : ℕ) (j : ℕ) (2 * r) := by
  simpa only [rvachevLegendreGramMatrixRat_apply] using
    rvachevLegendreGramEntryRat_eq_two_mul_sum_wignerThreeJZeroSqRat
      (i : ℕ) (j : ℕ)

/-- Every entry of the real up-law Legendre Gram matrix is twice the finite
sum of the analytic even Rvachev--Legendre coefficients against the real cast
of the total rational zero-row Wigner-square datum. -/
theorem upLegendreGramMatrix_apply_eq_two_mul_sum_wignerThreeJZeroSqRat
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (i j : Fin n) :
    upLegendreGramMatrix F n i j =
      2 * ∑ r ∈ range (((i : ℕ) + (j : ℕ)) / 2 + 1),
        rvachevLegendreCoefficient F r *
          (legendreWignerThreeJZeroSqRat
            (i : ℕ) (j : ℕ) (2 * r) : ℝ) := by
  calc
    upLegendreGramMatrix F n i j =
        ∑ r ∈ range (((i : ℕ) + (j : ℕ)) / 2 + 1),
          rvachevLegendreCoefficient F r *
            legendreGaunt (i : ℕ) (j : ℕ) (2 * r) :=
      upLegendreGramMatrix_apply_eq_sum_gaunt F hF n i j
    _ = ∑ r ∈ range (((i : ℕ) + (j : ℕ)) / 2 + 1),
          rvachevLegendreCoefficient F r *
            (2 * (legendreWignerThreeJZeroSqRat
              (i : ℕ) (j : ℕ) (2 * r) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [legendreGaunt_eq_two_mul_wignerThreeJZeroSqRat]
    _ = 2 * ∑ r ∈ range (((i : ℕ) + (j : ℕ)) / 2 + 1),
          rvachevLegendreCoefficient F r *
            (legendreWignerThreeJZeroSqRat
              (i : ℕ) (j : ℕ) (2 * r) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

end Fabius
