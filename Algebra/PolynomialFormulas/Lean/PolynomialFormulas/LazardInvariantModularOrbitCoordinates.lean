import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockZero
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockOne
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockTwo
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockThree
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockFour
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockFive
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockSix
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockSeven
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockEight
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockNine
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockTen
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockEleven
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockTwelve
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesBlockThirteen
import PolynomialFormulas.LazardInvariantModularOrbitCoordinatesRepresentativeBridge
import PolynomialFormulas.LazardInvariantModularDualCertificate
import Mathlib.Tactic

/-!
# Polynomial semantics for the modular C6 orbit coordinates

The finite coordinate space `Fin 132 → ZMod 3` is realized as the span of
literal cyclic orbit-sum polynomials.  The representative-separation
certificate is compiled in fourteen independent row-block modules imported
above, then assembled here.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularOrbitCoordinates

open scoped BigOperators
open Finset MvPolynomial
open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate

set_option autoImplicit false

noncomputable section

/-- The representative in column `j` lies in the orbit belonging to column
`i` exactly when the columns agree. -/
theorem degreeSevenRepresentative_mem_orbit_iff
    (i j : Fin 132) :
    degreeSevenRepresentative j ∈
        cyclicOrbitSupport (degreeSevenRepresentative i) ↔ i = j := by
  by_cases h₀ : i.1 < 10
  · exact degreeSevenRepresentative_mem_orbit_iff_block_zero i j h₀
  by_cases h₁ : i.1 < 20
  · exact degreeSevenRepresentative_mem_orbit_iff_block_one i j
      ⟨Nat.le_of_not_gt h₀, h₁⟩
  by_cases h₂ : i.1 < 30
  · exact degreeSevenRepresentative_mem_orbit_iff_block_two i j
      ⟨Nat.le_of_not_gt h₁, h₂⟩
  by_cases h₃ : i.1 < 40
  · exact degreeSevenRepresentative_mem_orbit_iff_block_three i j
      ⟨Nat.le_of_not_gt h₂, h₃⟩
  by_cases h₄ : i.1 < 50
  · exact degreeSevenRepresentative_mem_orbit_iff_block_four i j
      ⟨Nat.le_of_not_gt h₃, h₄⟩
  by_cases h₅ : i.1 < 60
  · exact degreeSevenRepresentative_mem_orbit_iff_block_five i j
      ⟨Nat.le_of_not_gt h₄, h₅⟩
  by_cases h₆ : i.1 < 70
  · exact degreeSevenRepresentative_mem_orbit_iff_block_six i j
      ⟨Nat.le_of_not_gt h₅, h₆⟩
  by_cases h₇ : i.1 < 80
  · exact degreeSevenRepresentative_mem_orbit_iff_block_seven i j
      ⟨Nat.le_of_not_gt h₆, h₇⟩
  by_cases h₈ : i.1 < 90
  · exact degreeSevenRepresentative_mem_orbit_iff_block_eight i j
      ⟨Nat.le_of_not_gt h₇, h₈⟩
  by_cases h₉ : i.1 < 100
  · exact degreeSevenRepresentative_mem_orbit_iff_block_nine i j
      ⟨Nat.le_of_not_gt h₈, h₉⟩
  by_cases h₁₀ : i.1 < 110
  · exact degreeSevenRepresentative_mem_orbit_iff_block_ten i j
      ⟨Nat.le_of_not_gt h₉, h₁₀⟩
  by_cases h₁₁ : i.1 < 120
  · exact degreeSevenRepresentative_mem_orbit_iff_block_eleven i j
      ⟨Nat.le_of_not_gt h₁₀, h₁₁⟩
  by_cases h₁₂ : i.1 < 130
  · exact degreeSevenRepresentative_mem_orbit_iff_block_twelve i j
      ⟨Nat.le_of_not_gt h₁₁, h₁₂⟩
  exact degreeSevenRepresentative_mem_orbit_iff_block_thirteen i j
    ⟨Nat.le_of_not_gt h₁₂, i.isLt⟩

/-- Interpret a 132-entry coordinate vector as an actual polynomial linear
combination of the 132 degree-seven cyclic orbit sums. -/
def degreeSevenOrbitCoordinateMap :
    DegreeSevenCoordinates →ₗ[F3] MvPolynomial (Fin 6) F3 :=
  Fintype.linearCombination F3 degreeSevenOrbitPolynomial

/-- Reading the coefficient at the canonical representative of column `j`
recovers the original `j`th coordinate. -/
theorem coeff_degreeSevenOrbitCoordinateMap
    (v : DegreeSevenCoordinates) (j : Fin 132) :
    (degreeSevenOrbitCoordinateMap v).coeff
        (Finsupp.equivFunOnFinite.symm (degreeSevenRepresentative j)) =
      v j := by
  classical
  change
    (MvPolynomial.lcoeff F3
      (Finsupp.equivFunOnFinite.symm (degreeSevenRepresentative j)))
        (degreeSevenOrbitCoordinateMap v) = v j
  rw [degreeSevenOrbitCoordinateMap, Fintype.linearCombination_apply,
    map_sum]
  simp [degreeSevenOrbitPolynomial, coeff_cyclicOrbitPolynomial,
    degreeSevenRepresentative_mem_orbit_iff, eq_comm]

/-- The finite coordinates embed faithfully into the actual polynomial ring. -/
theorem degreeSevenOrbitCoordinateMap_injective :
    Function.Injective degreeSevenOrbitCoordinateMap := by
  intro v w hvw
  funext j
  have hcoeff := congrArg
    (MvPolynomial.coeff
      (Finsupp.equivFunOnFinite.symm (degreeSevenRepresentative j))) hvw
  simpa only [coeff_degreeSevenOrbitCoordinateMap] using hcoeff

/-- Consequently the 132 literal cyclic orbit-sum polynomials are linearly
independent over `ZMod 3`. -/
theorem degreeSevenOrbitPolynomial_linearIndependent :
    LinearIndependent F3 degreeSevenOrbitPolynomial := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  exact degreeSevenOrbitCoordinateMap_injective

/-- The actual polynomial subspace represented by the 132 orbit coordinates. -/
abbrev DegreeSevenOrbitPolynomialSpace :=
  LinearMap.range degreeSevenOrbitCoordinateMap

/-- Linear equivalence between the finite certificate coordinates and their
literal polynomial realization. -/
def degreeSevenOrbitCoordinateEquiv :
    DegreeSevenCoordinates ≃ₗ[F3] DegreeSevenOrbitPolynomialSpace :=
  LinearEquiv.ofInjective degreeSevenOrbitCoordinateMap
    degreeSevenOrbitCoordinateMap_injective

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularOrbitCoordinates
