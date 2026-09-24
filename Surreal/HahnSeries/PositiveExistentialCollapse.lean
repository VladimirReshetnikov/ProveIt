import Surreal.Algebra.PositiveExistentialDefinability
import Surreal.HahnSeries.ConstantTermGraph
import Surreal.HahnSeries.IdealMultipliers
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Positive-existential collapse in full Hahn coefficient pullbacks

All clauses of `odg:def:thm:collapse`, for any injectively embedded ordinary
coefficient ring. Nontriviality of the exponent group is needed only to
supply a nonzero purely infinite monomial for the displayed examples.
-/

namespace Surreal.HahnSeries
open FirstOrder FirstOrder.Language _root_.HahnSeries
noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [CommRing O]

local instance collapseRingStructure (i : O →+* K) :
    FirstOrder.Ring.CompatibleRing (coefficientRestrictedSubring (Γ := Γ) i) :=
  FirstOrder.Ring.compatibleRingOfRing _

/-- Constant extraction fixes the section of the prescribed coefficient ring. -/
@[simp] theorem coefficientRestrictedRetraction_constants (i : O →+* K) (hi : Function.Injective i)
    (a : O) : coefficientRestrictedRetraction (Γ := Γ) i hi (coefficientRestrictedConstants i a) = a :=
  CoefficientPullback.retraction_sectionMap (nonpositiveConstantCoeff (Γ := Γ) (R := K))
    i hi nonpositiveConstants nonpositiveConstantCoeff_constants a

/-- Every nonempty purely infinite fiber of a positive-existential set forces zero into the set. -/
theorem coefficientRestricted_not_positiveExistentialDefinable_of_purelyInfinite
    (i : O →+* K) (hi : Function.Injective i)
    {D : Set (coefficientRestrictedSubring (Γ := Γ) i)} {x : coefficientRestrictedSubring (Γ := Γ) i}
    (hx : x ∈ D) (hpi : x.val ∈ purelyInfiniteIdeal) (hzero : (0 : coefficientRestrictedSubring i) ∉ D) :
    ¬ PositiveExistentialDefinable Language.ring (coefficientRestrictedConstants i)
      {v : Fin 1 → coefficientRestrictedSubring (Γ := Γ) i | v 0 ∈ D} := by
  apply not_positiveExistentialDefinable_of_retraction (coefficientRestrictedRetraction i hi)
    (coefficientRestrictedConstants i)
    (coefficientRestrictedRetraction_constants (Γ := Γ) i hi) hx
  · exact (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi x).mpr hpi
  · exact hzero

/-- A negative Hahn exponent gives an element of every coefficient pullback, independently of O. -/
def purelyInfiniteMonomial (i : O →+* K) (g : Γ) (hg : g < 0) : coefficientRestrictedSubring (Γ := Γ) i :=
  purelyInfiniteRestricted i (single g 1) (purelyInfiniteSeries_single g hg 1)

theorem purelyInfiniteMonomial_ne_zero (i : O →+* K) (g : Γ) (hg : g < 0) :
    purelyInfiniteMonomial i g hg ≠ 0 := by
  intro h
  have he := congrArg (fun x : coefficientRestrictedSubring i => x.val.val) h
  change single g (1 : K) = 0 at he
  simp at he

theorem purelyInfiniteMonomial_mem (i : O →+* K) (g : Γ) (hg : g < 0) :
    (purelyInfiniteMonomial i g hg).val ∈ purelyInfiniteIdeal := by
  change (single g (1 : K)).coeff 0 = 0
  exact purelyInfiniteSeries_single g hg (1 : K) 0 le_rfl

/-- Nonzero purely infinite elements exist whenever the exponent group is nontrivial. -/
theorem coefficientRestricted_exists_nonzero_purelyInfinite [Nontrivial Γ] (i : O →+* K) :
    ∃ x : coefficientRestrictedSubring (Γ := Γ) i, x ≠ 0 ∧ x.val ∈ purelyInfiniteIdeal := by
  obtain ⟨g, hg⟩ := exists_lt (0 : Γ)
  exact ⟨purelyInfiniteMonomial i g hg, purelyInfiniteMonomial_ne_zero i g hg,
    purelyInfiniteMonomial_mem i g hg⟩

/-- No nonzero element of the purely infinite ideal is an ordinary coefficient constant. -/
theorem coefficientRestricted_purelyInfinite_not_constant (i : O →+* K) (hi : Function.Injective i)
    {x : coefficientRestrictedSubring (Γ := Γ) i} (hx : x ≠ 0) (hpi : x.val ∈ purelyInfiniteIdeal) :
    x ∉ Set.range (coefficientRestrictedConstants i) := by
  rintro ⟨a, ha⟩
  have hct : coefficientRestrictedRetraction i hi x = 0 :=
    (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi x).mpr hpi
  have ha0 : a = 0 := by
    have he := congrArg (coefficientRestrictedRetraction i hi) ha
    rw [coefficientRestrictedRetraction_constants] at he
    exact he.trans hct
  apply hx
  rw [← ha, ha0, map_zero]

/-- The nonzero set is not positively existentially definable with coefficient parameters. -/
theorem coefficientRestricted_nonzero_not_positiveExistentialDefinable [Nontrivial Γ]
    (i : O →+* K) (hi : Function.Injective i) :
    ¬ PositiveExistentialDefinable Language.ring (coefficientRestrictedConstants i)
      {v : Fin 1 → coefficientRestrictedSubring (Γ := Γ) i | v 0 ≠ 0} := by
  obtain ⟨x, hx, hpi⟩ := coefficientRestricted_exists_nonzero_purelyInfinite (Γ := Γ) i
  exact coefficientRestricted_not_positiveExistentialDefinable_of_purelyInfinite i hi
    (D := {x | x ≠ 0}) hx hpi (by simp)

/-- The complement of the coefficient subring is not positively existentially definable. -/
theorem coefficientRestricted_nonconstant_not_positiveExistentialDefinable [Nontrivial Γ]
    (i : O →+* K) (hi : Function.Injective i) :
    ¬ PositiveExistentialDefinable Language.ring (coefficientRestrictedConstants i)
      {v : Fin 1 → coefficientRestrictedSubring (Γ := Γ) i |
        v 0 ∉ Set.range (coefficientRestrictedConstants i)} := by
  obtain ⟨x, hx, hpi⟩ := coefficientRestricted_exists_nonzero_purelyInfinite (Γ := Γ) i
  apply coefficientRestricted_not_positiveExistentialDefinable_of_purelyInfinite i hi
    (D := {x | x ∉ Set.range (coefficientRestrictedConstants i)})
    (coefficientRestricted_purelyInfinite_not_constant i hi hx hpi) hpi
  exact fun h => h ⟨0, map_zero _⟩

/-- The purely infinite ideal with zero removed is not positively existentially definable. -/
theorem coefficientRestricted_puncturedIdeal_not_positiveExistentialDefinable [Nontrivial Γ]
    (i : O →+* K) (hi : Function.Injective i) :
    ¬ PositiveExistentialDefinable Language.ring (coefficientRestrictedConstants i)
      {v : Fin 1 → coefficientRestrictedSubring (Γ := Γ) i |
        (v 0).val ∈ purelyInfiniteIdeal ∧ v 0 ≠ 0} := by
  obtain ⟨x, hx, hpi⟩ := coefficientRestricted_exists_nonzero_purelyInfinite (Γ := Γ) i
  exact coefficientRestricted_not_positiveExistentialDefinable_of_purelyInfinite i hi
    (D := {x | x.val ∈ purelyInfiniteIdeal ∧ x ≠ 0}) ⟨hpi, hx⟩ hpi (by simp)

/-- The monomial witness is positive in the actual lexicographic Hahn order. -/
theorem purelyInfiniteMonomial_pos [LinearOrder K] [IsStrictOrderedRing K]
    (i : O →+* K) (g : Γ) (hg : g < 0) :
    0 < toLex (purelyInfiniteMonomial i g hg).val.val := by
  apply leadingCoeff_pos_iff.mp
  change 0 < (single g (1 : K)).leadingCoeff
  simp

/-- Over an ordered coefficient field, even the strictly positive cone is excluded. -/
theorem coefficientRestricted_positive_not_positiveExistentialDefinable [Nontrivial Γ]
    [LinearOrder K] [IsStrictOrderedRing K] (i : O →+* K) (hi : Function.Injective i) :
    ¬ PositiveExistentialDefinable Language.ring (coefficientRestrictedConstants i)
      {v : Fin 1 → coefficientRestrictedSubring (Γ := Γ) i | 0 < toLex (v 0).val.val} := by
  obtain ⟨g, hg⟩ := exists_lt (0 : Γ)
  exact coefficientRestricted_not_positiveExistentialDefinable_of_purelyInfinite i hi
    (D := {x | 0 < toLex x.val.val}) (purelyInfiniteMonomial_pos i g hg)
    (purelyInfiniteMonomial_mem i g hg) (by simp)

end
end Surreal.HahnSeries
