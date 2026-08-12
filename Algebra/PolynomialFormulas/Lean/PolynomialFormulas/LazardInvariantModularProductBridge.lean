import PolynomialFormulas.LazardInvariantModularProductBridgeBlockZero
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockOne
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockTwo
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockThree
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockFour
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockFive
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockSix
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockSeven
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockEight
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockNine
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockTen
import PolynomialFormulas.LazardInvariantModularProductBridgeBlockEleven
import PolynomialFormulas.LazardInvariantModularProductBridgeAdapter
import PolynomialFormulas.LazardInvariantModularProductBridgeRemainingRows
import PolynomialFormulas.LazardInvariantModularProductBridgeStagedTail
import PolynomialFormulas.LazardInvariantModularProductBridgeStagedTail146To158
import Mathlib.Tactic

/-!
# Literal polynomial semantics for the 159 modular product rows

The modular obstruction encodes 159 rows.  A source row consists of a
positive elementary-symmetric degree `d` and a canonical cyclic orbit in
degree `7-d`.  This file identifies the encoded row with the literal
polynomial

`MvPolynomial.esymm (Fin 6) (ZMod 3) d * cyclicOrbitPolynomial source`.

The equality is a closed finite statement.  The executable row checks are
split into bounded source intervals, then a generic coefficient-to-polynomial
adapter reconstructs the literal products.  Four legacy tail shards still
check polynomial equality directly.  No custom Gaussian-elimination
correctness theorem is used here.

The final theorem identifies the span of the 159 encoded coordinate rows,
after the faithful polynomial realization, with the span of those literal
elementary-symmetric products.  This is the positive symmetric-product
subspace needed in degree seven.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open scoped BigOperators
open Finset MvPolynomial
open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 80000000

noncomputable section

/-- Every one of the 159 coordinate rows denotes its advertised literal
elementary-symmetric product. -/
theorem degreeSevenLiteralProduct_eq_encoded (i : Fin 159) :
    degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  by_cases h₀ : i.1 < 8
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_zero i h₀)
  by_cases h₁ : i.1 < 16
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_one i
        ⟨Nat.le_of_not_gt h₀, h₁⟩)
  by_cases h₂ : i.1 < 24
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_two i
        ⟨Nat.le_of_not_gt h₁, h₂⟩)
  by_cases h₃ : i.1 < 32
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_three i
        ⟨Nat.le_of_not_gt h₂, h₃⟩)
  by_cases h₄ : i.1 < 40
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_four i
        ⟨Nat.le_of_not_gt h₃, h₄⟩)
  by_cases h₅ : i.1 < 48
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_five i
        ⟨Nat.le_of_not_gt h₄, h₅⟩)
  by_cases h₆ : i.1 < 56
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_six i
        ⟨Nat.le_of_not_gt h₅, h₆⟩)
  by_cases h₇ : i.1 < 64
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_seven i
        ⟨Nat.le_of_not_gt h₆, h₇⟩)
  by_cases h₈ : i.1 < 72
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_eight i
        ⟨Nat.le_of_not_gt h₇, h₈⟩)
  by_cases h₉ : i.1 < 80
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_nine i
        ⟨Nat.le_of_not_gt h₈, h₉⟩)
  by_cases h₁₀ : i.1 < 82
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_ten i
        ⟨Nat.le_of_not_gt h₉, h₁₀⟩)
  by_cases h₁₁ : i.1 < 84
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_block_eleven i
        ⟨Nat.le_of_not_gt h₁₀, h₁₁⟩)
  by_cases hremaining : i.1 < 120
  · exact degreeSevenLiteralProduct_eq_encoded_of_productCoefficients i
      (degreeSevenProductRow_eq_productCoefficient_rows_eightyFour_to_oneTwenty i
        ⟨Nat.le_of_not_gt h₁₁, hremaining⟩)
  by_cases h₁₄₆ : i.1 < 146
  · exact degreeSevenLiteralProduct_eq_encoded_rows120To145 i
      ⟨Nat.le_of_not_gt hremaining, h₁₄₆⟩
  exact degreeSevenLiteralProduct_eq_encoded_rows146To158 i
    ⟨Nat.le_of_not_gt h₁₄₆, i.isLt⟩

/-! ## Identification of the positive symmetric-product subspace -/

/-- The actual polynomial subspace spanned by all products
`e_d * (degree-(7-d) cyclic orbit sum)` with `1 ≤ d ≤ 6`. -/
def degreeSevenPositiveSymmetricProductSubspace :
    Submodule F3 (MvPolynomial (Fin 6) F3) :=
  Submodule.span F3 (Set.range degreeSevenLiteralProduct)

/-- Mapping the certified coordinate-row span into the polynomial ring gives
exactly the literal positive symmetric-product subspace. -/
theorem degreeSevenProductSubspace_map_eq_positiveSymmetricProductSubspace :
    degreeSevenProductSubspace.map degreeSevenOrbitCoordinateMap =
      degreeSevenPositiveSymmetricProductSubspace := by
  apply le_antisymm
  · rw [degreeSevenProductSubspace, LinearMap.map_span_le]
    rintro _ ⟨i, rfl⟩
    change degreeSevenOrbitCoordinateMap (degreeSevenProductRow i) ∈
      degreeSevenPositiveSymmetricProductSubspace
    rw [← degreeSevenEncodedProduct_eq_coordinateMap]
    rw [← degreeSevenLiteralProduct_eq_encoded]
    exact Submodule.subset_span (Set.mem_range_self i)
  · rw [degreeSevenPositiveSymmetricProductSubspace]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [degreeSevenLiteralProduct_eq_encoded,
      degreeSevenEncodedProduct_eq_coordinateMap]
    change degreeSevenOrbitCoordinateMap (degreeSevenProductRow i) ∈
      degreeSevenProductSubspace.map degreeSevenOrbitCoordinateMap
    refine ⟨degreeSevenProductRow i, ?_, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)

/-! ## Intrinsic module-product description -/

/-- Multiplication by the `d`th elementary symmetric polynomial, as an
`F3`-linear map on the full polynomial ring. -/
def elementaryMulLinear (d : ℕ) :
    MvPolynomial (Fin 6) F3 →ₗ[F3] MvPolynomial (Fin 6) F3 :=
  LinearMap.mulLeft F3 (MvPolynomial.esymm (Fin 6) F3 d)

/-- Intrinsic degree-seven positive symmetric-module product subspace: for
each `k = 0,...,5`, multiply the degree-`6-k` cyclic orbit-sum subspace by
`e_(k+1)`, then add the six images. -/
def degreeSevenPositiveSymmetricModuleSubspace :
    Submodule F3 (MvPolynomial (Fin 6) F3) :=
  ⨆ k : Fin 6,
    (cyclicOrbitSumSubspace (6 - k.1)).map
      (elementaryMulLinear (k.1 + 1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- Every encoded source has exactly the advertised form
`(k+1, degree-(6-k) orbit representative)`. -/
theorem degreeSevenProductSource_classification :
    ∀ i : Fin 159, ∃ k : Fin 6,
      (degreeSevenProductSource i).1 = k.1 + 1 ∧
      (degreeSevenProductSource i).2 ∈
        (orbitRepresentatives (6 - k.1)).toFinset := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- Conversely, every positive elementary degree and every canonical lower
orbit representative occurs among the 159 encoded sources. -/
theorem degreeSevenProductSource_complete :
    ∀ (k : Fin 6) (a : OrbitRepresentative (6 - k.1)),
      ∃ i : Fin 159,
        degreeSevenProductSource i = (k.1 + 1, a.1) := by
  decide

/-- The span of the 159 literal products is exactly the intrinsic sum
`Σ_(d=1)^6 e_d · (cyclic orbit-sum space in degree 7-d)`. -/
theorem degreeSevenPositiveSymmetricProductSubspace_eq_moduleSubspace :
    degreeSevenPositiveSymmetricProductSubspace =
      degreeSevenPositiveSymmetricModuleSubspace := by
  apply le_antisymm
  · rw [degreeSevenPositiveSymmetricProductSubspace]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rcases degreeSevenProductSource_classification i with
      ⟨k, hdegree, hrepresentative⟩
    apply (le_iSup
      (fun k : Fin 6 =>
        (cyclicOrbitSumSubspace (6 - k.1)).map
          (elementaryMulLinear (k.1 + 1))) k)
    refine ⟨cyclicOrbitPolynomial (degreeSevenProductSource i).2, ?_, ?_⟩
    · exact Submodule.subset_span
        ⟨⟨(degreeSevenProductSource i).2, hrepresentative⟩, rfl⟩
    · simp [degreeSevenLiteralProduct, elementaryMulLinear, hdegree]
  · rw [degreeSevenPositiveSymmetricModuleSubspace]
    apply iSup_le
    intro k
    rw [cyclicOrbitSumSubspace, LinearMap.map_span_le]
    rintro _ ⟨a, rfl⟩
    rcases degreeSevenProductSource_complete k a with ⟨i, hi⟩
    have hproduct :
        elementaryMulLinear (k.1 + 1) (cyclicOrbitPolynomial a.1) =
          degreeSevenLiteralProduct i := by
      simp [elementaryMulLinear, degreeSevenLiteralProduct, hi]
    rw [hproduct]
    exact Submodule.subset_span (Set.mem_range_self i)

/-- Combining the finite row identity with the intrinsic description: the
mapped coordinate row span is the literal degree-seven positive
symmetric-module product subspace. -/
theorem degreeSevenProductSubspace_map_eq_positiveSymmetricModuleSubspace :
    degreeSevenProductSubspace.map degreeSevenOrbitCoordinateMap =
      degreeSevenPositiveSymmetricModuleSubspace := by
  rw [degreeSevenProductSubspace_map_eq_positiveSymmetricProductSubspace,
    degreeSevenPositiveSymmetricProductSubspace_eq_moduleSubspace]

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
