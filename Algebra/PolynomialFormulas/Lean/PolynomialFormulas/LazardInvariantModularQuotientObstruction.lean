import PolynomialFormulas.LazardInvariantModularProductBridge
import PolynomialFormulas.LazardInvariantModularDualCertificate
import PolynomialFormulas.LazardDualQuotientCertificate
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# A compact literal-quotient obstruction in characteristic three

The staged modular product bridge identifies the 159 coordinate rows with
literal polynomial products.  This file transports the existing seventeen
dual-certificate classes through that faithful quotient map and proves the
correct finite-dimensional conclusion: those seventeen classes cannot all lie
in the span of any sixteen prescribed classes.  This is the stable semantic
core needed by the unfinished homogeneous-free-basis contradiction, without
depending on its larger tower-basis API.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularQuotientObstruction

open scoped BigOperators
open Finset MvPolynomial
open Module
open LazardDualQuotientCertificate
open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates
open LazardInvariantModularProductBridge

set_option autoImplicit false

noncomputable section

abbrev LiteralDegreeSevenProductSubspace :
    Submodule F3 (MvPolynomial (Fin 6) F3) :=
  degreeSevenProductSubspace.map degreeSevenOrbitCoordinateMap

abbrev LiteralDegreeSevenQuotient :=
  MvPolynomial (Fin 6) F3 ⧸ LiteralDegreeSevenProductSubspace

def coordinateQuotientToLiteralQuotient :
    (DegreeSevenCoordinates ⧸ degreeSevenProductSubspace) →ₗ[F3]
      LiteralDegreeSevenQuotient :=
  degreeSevenProductSubspace.mapQ LiteralDegreeSevenProductSubspace
    degreeSevenOrbitCoordinateMap
    (Submodule.le_comap_map degreeSevenOrbitCoordinateMap
      degreeSevenProductSubspace)

theorem coordinateQuotientToLiteralQuotient_injective :
    Function.Injective coordinateQuotientToLiteralQuotient :=
  quotientMap_injective_of_injective degreeSevenProductSubspace
    degreeSevenOrbitCoordinateMap degreeSevenOrbitCoordinateMap_injective

def literalTestClass (j : Fin 17) : LiteralDegreeSevenQuotient :=
  coordinateQuotientToLiteralQuotient
    (degreeSevenProductSubspace.mkQ (testVector j))

theorem literalTestClass_linearIndependent :
    LinearIndependent F3 literalTestClass := by
  have h := degreeSeven_testClasses_linearIndependent.map'
    coordinateQuotientToLiteralQuotient
    (LinearMap.ker_eq_bot.mpr
      coordinateQuotientToLiteralQuotient_injective)
  change LinearIndependent F3
    (fun j => coordinateQuotientToLiteralQuotient
      (degreeSevenProductSubspace.mkQ (testVector j))) at h
  exact h

theorem literalTestClass_not_spanned_by_sixteen
    (generators : Fin 16 → LiteralDegreeSevenQuotient) :
    ¬ (∀ j : Fin 17, literalTestClass j ∈
      Submodule.span F3 (Set.range generators)) := by
  intro hcontain
  let tests : Submodule F3 LiteralDegreeSevenQuotient :=
    Submodule.span F3 (Set.range literalTestClass)
  let generated : Submodule F3 LiteralDegreeSevenQuotient :=
    Submodule.span F3 (Set.range generators)
  have htests_le : tests ≤ generated := by
    change Submodule.span F3 (Set.range literalTestClass) ≤ generated
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hcontain j
  letI : Module.Finite F3 generated :=
    Module.Finite.span_of_finite F3 (Set.finite_range generators)
  have htests_rank : Module.finrank F3 tests = 17 := by
    change Module.finrank F3
      (Submodule.span F3 (Set.range literalTestClass)) = 17
    rw [finrank_span_eq_card literalTestClass_linearIndependent]
    rfl
  have hgenerated_rank : Module.finrank F3 generated ≤ 16 := by
    change (Set.range generators).finrank F3 ≤ 16
    simpa using finrank_range_le_card generators
  have hmono : Module.finrank F3 tests ≤ Module.finrank F3 generated :=
    Submodule.finrank_mono htests_le
  omega

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularQuotientObstruction
