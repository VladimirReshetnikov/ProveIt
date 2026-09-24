import Surreal.Algebra.QuantifierFreeRetraction
import Surreal.Algebra.ArithmeticGuards
import Surreal.HahnSeries.PositiveExistentialCollapse
import Surreal.HahnSeries.Characteristic

/-!
# No quantifier-free definitions of the ideal or constants in full Hahn pullbacks

All clauses of `odg:def:prop:notqf`, including an explicit formula with no
quantifier-free equivalent modulo the complete theory. All ring elements
are available as parameters in the nondefinability assertions.
-/

namespace Surreal.HahnSeries
open FirstOrder FirstOrder.Language
noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Nontrivial Γ] [Field K] [CharZero K] [CommRing O]

local instance quantifierFreeRingStructure (i : O →+* K) :
    FirstOrder.Ring.CompatibleRing (coefficientRestrictedSubring (Γ := Γ) i) :=
  FirstOrder.Ring.compatibleRingOfRing _

/-- The purely infinite ideal has no quantifier-free definition even with all ring parameters. -/
theorem coefficientRestricted_ideal_not_quantifierFreeDefinable (i : O →+* K)
    (hi : Function.Injective i) :
    ¬ QuantifierFree.Definable₁ (id : coefficientRestrictedSubring (Γ := Γ) i → _)
      {x | x.val ∈ purelyInfiniteIdeal} := by
  letI : CharZero O := i.charZero
  obtain ⟨w, hw, hpi⟩ := coefficientRestricted_exists_nonzero_purelyInfinite (Γ := Γ) i
  have hct : coefficientRestrictedRetraction i hi w = 0 :=
    (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi w).mpr hpi
  have hs : {x : coefficientRestrictedSubring (Γ := Γ) i | x.val ∈ purelyInfiniteIdeal} =
      {x | coefficientRestrictedRetraction i hi x = 0} := by
    ext x
    exact (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi x).symm
  rw [hs]
  exact QuantifierFree.kernel_not_definable₁ (coefficientRestrictedRetraction i hi) hw hct id

/-- The coefficient subring also has no quantifier-free definition with arbitrary ring parameters. -/
theorem coefficientRestricted_constants_not_quantifierFreeDefinable (i : O →+* K)
    (hi : Function.Injective i) :
    ¬ QuantifierFree.Definable₁ (id : coefficientRestrictedSubring (Γ := Γ) i → _)
      (Set.range (coefficientRestrictedConstants i)) := by
  letI : CharZero O := i.charZero
  obtain ⟨w, hw, hpi⟩ := coefficientRestricted_exists_nonzero_purelyInfinite (Γ := Γ) i
  exact QuantifierFree.constants_not_definable₁ (coefficientRestrictedRetraction i hi)
    (coefficientRestrictedConstants i) (coefficientRestrictedRetraction_constants i hi) hw
    ((CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi w).mpr hpi) id

/-- Whenever Xi defines the coefficients, it explicitly witnesses failure of quantifier elimination. -/
theorem coefficientRestricted_no_quantifierFree_equivalent (i : O →+* K) (hi : Function.Injective i)
    (hno : ∀ a : O, IntersectivePolynomial.value a ≠ 0)
    (hord : ∀ a : O, DiophantineConstants.Xi a) :
    ¬ ∃ ψ : Language.ring.Formula (Fin 1), ψ.IsQF ∧
      Language.ring.completeTheory (coefficientRestrictedSubring (Γ := Γ) i) ⊨ᵇ
        ArithmeticGuards.integerGuard.iff ψ := by
  letI : CharZero O := i.charZero
  obtain ⟨w, hw, hpi⟩ := coefficientRestricted_exists_nonzero_purelyInfinite (Γ := Γ) i
  have hct : coefficientRestrictedRetraction i hi w = 0 :=
    (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi w).mpr hpi
  apply QuantifierFree.no_quantifierFree_equivalent_in_completeTheory
    (RetractionInfiniteSets.constants_infinite (coefficientRestrictedRetraction i hi)
      (coefficientRestrictedConstants i) (coefficientRestrictedRetraction_constants i hi))
    (RetractionInfiniteSets.constants_complement_infinite (coefficientRestrictedRetraction i hi)
      (coefficientRestrictedConstants i) (coefficientRestrictedRetraction_constants i hi) hw hct)
  intro x
  rw [ArithmeticGuards.realize_integerGuard,
    intermediate_xi_iff i hi hno hord _ (coefficientRestricted_constants_intersection i)]
  exact exists_congr fun a => ⟨fun h => Subtype.ext h.symm, fun h => (congrArg Subtype.val h).symm⟩

/-- In the integer case, the concrete parameter-free Xi formula has no quantifier-free equivalent. -/
theorem integerRestricted_no_quantifierFree_equivalent :
    ¬ ∃ ψ : Language.ring.Formula (Fin 1), ψ.IsQF ∧
      Language.ring.completeTheory (coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)) ⊨ᵇ
        ArithmeticGuards.integerGuard.iff ψ :=
  coefficientRestricted_no_quantifierFree_equivalent (Int.castRingHom K) Int.cast_injective
    IntersectivePolynomial.integer_value_ne_zero DiophantineConstants.integer_xi

/-- The same explicit failure holds for every Gaussian coefficient pullback. -/
theorem gaussianRestricted_no_quantifierFree_equivalent (i : GaussianInt →+* K)
    (hi : Function.Injective i) :
    ¬ ∃ ψ : Language.ring.Formula (Fin 1), ψ.IsQF ∧
      Language.ring.completeTheory (coefficientRestrictedSubring (Γ := Γ) i) ⊨ᵇ
        ArithmeticGuards.integerGuard.iff ψ :=
  coefficientRestricted_no_quantifierFree_equivalent i hi
    IntersectivePolynomial.gaussian_value_ne_zero DiophantineConstants.gaussian_xi

end
end Surreal.HahnSeries
