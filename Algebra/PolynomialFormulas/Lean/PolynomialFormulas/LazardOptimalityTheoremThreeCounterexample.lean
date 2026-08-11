import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.Tactic.NormNum
import PolynomialFormulas.LazardOptimalityCyclicQuinticCounterexample

/-!
# A degree obstruction to Lazard's Theorem 3

This file begins the formal counterexample to Theorem 3 of Lazard's paper.
It first isolates the field theory that is independent of the quintic formula.

Inside the common `55`th-cyclotomic ambient field, let

* `S = ℚ(zeta11 + zeta11⁻¹)`, the cyclic quintic field; and
* `W = ℚ(zeta5)`, the fifth-cyclotomic field.

Their degrees are respectively `5` and `4`, so they are linearly disjoint and
`S ⊔ W` has degree `20`.  It therefore cannot embed into the degree-`10`
field `ElevenField`.

The final section is deliberately conditional.  A
`CyclicLazardFormulaFieldProfile K0 E` records the exact formula-field facts
still needed to identify a concrete one-root Lazard formula field `E` with
`S ⊔ W`.  In particular, it does not assert that such a profile exists.  No
formula identity, branch condition, or Galois-descent assertion is hidden in
an axiom.
-/

namespace LeanProofs.PolynomialFormulas.LazardOptimalityTheoremThreeCounterexample

open Polynomial
open IntermediateField
open LeanProofs.PolynomialFormulas.LazardOptimalityCyclotomicCounterexample
open LeanProofs.PolynomialFormulas.LazardOptimalityCyclicQuinticCounterexample

set_option autoImplicit false

noncomputable section

local instance five_prime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## The cyclic quintic and fifth-cyclotomic subfields -/

/-- The cyclic-quintic root, now regarded as an element of the common
`55`th-cyclotomic ambient field. -/
noncomputable def cyclicQuinticRootAmbient : Ambient :=
  algebraMap ElevenField Ambient cyclicQuinticRoot

/-- The real cyclic quintic field `S = ℚ(zeta11 + zeta11⁻¹)`. -/
noncomputable def CyclicQuinticField : IntermediateField ℚ Ambient :=
  ℚ⟮cyclicQuinticRootAmbient⟯

/-- The fifth-cyclotomic field `W = ℚ(zeta5)` in the same ambient field. -/
noncomputable abbrev FifthCyclotomicField : IntermediateField ℚ Ambient :=
  ℚ⟮zeta5⟯

/-- Passing from `ElevenField` to the common ambient field does not change
the minimal polynomial of the cyclic-quintic root. -/
theorem cyclicQuinticRootAmbient_minpoly :
    minpoly ℚ cyclicQuinticRootAmbient = cyclicQuinticQ := by
  calc
    minpoly ℚ cyclicQuinticRootAmbient =
        minpoly ℚ cyclicQuinticRoot := by
      simpa only [cyclicQuinticRootAmbient,
        IsScalarTower.toAlgHom_apply] using
        minpoly.algHom_eq
          (IsScalarTower.toAlgHom ℚ ElevenField Ambient)
          (algebraMap ElevenField Ambient).injective
          cyclicQuinticRoot
    _ = cyclicQuinticQ := cyclicQuinticQ_eq_minpoly.symm

theorem cyclicQuinticRootAmbient_isIntegral :
    IsIntegral ℚ cyclicQuinticRootAmbient :=
  IsIntegral.of_finite ℚ cyclicQuinticRootAmbient

/-- The real cyclic quintic field has degree five over `ℚ`. -/
theorem cyclicQuinticField_finrank :
    Module.finrank ℚ CyclicQuinticField = 5 := by
  rw [CyclicQuinticField,
    IntermediateField.adjoin.finrank cyclicQuinticRootAmbient_isIntegral,
    cyclicQuinticRootAmbient_minpoly, cyclicQuinticQ_natDegree]

/-- The cyclic quintic field is visibly a subfield of the competing
eleventh-cyclotomic radical field. -/
theorem cyclicQuinticField_le_elevenField :
    CyclicQuinticField ≤ ElevenField := by
  rw [CyclicQuinticField, adjoin_simple_le_iff]
  simpa only [cyclicQuinticRootAmbient, IntermediateField.algebraMap_apply] using
    cyclicQuinticRoot.property

/-- Adjoining the displayed primitive fifth root produces an intrinsic
fifth-cyclotomic extension. -/
noncomputable instance fifthCyclotomicField_isCyclotomicExtension :
    IsCyclotomicExtension {5} ℚ FifthCyclotomicField := by
  have hAlgebra :
      FifthCyclotomicField.algebra =
        (DivisionRing.toRatAlgebra : Algebra ℚ FifthCyclotomicField) :=
    Subsingleton.elim _ _
  rw [← hAlgebra]
  simpa only [FifthCyclotomicField] using
    zeta5_isPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension ℚ

/-- The fifth-cyclotomic field has degree four over `ℚ`. -/
theorem fifthCyclotomicField_finrank :
    Module.finrank ℚ FifthCyclotomicField = 4 := by
  rw [IsCyclotomicExtension.finrank FifthCyclotomicField
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 5))]
  exact (Nat.totient_prime Nat.prime_five).trans (by decide)

/-- Coprime degrees make the cyclic quintic and fifth-cyclotomic fields
linearly disjoint. -/
theorem cyclicQuinticField_linearDisjoint_fifthCyclotomicField :
    CyclicQuinticField.LinearDisjoint FifthCyclotomicField := by
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  rw [cyclicQuinticField_finrank, fifthCyclotomicField_finrank]
  norm_num

/-- The two fields have trivial intersection over `ℚ`. -/
theorem cyclicQuinticField_inf_fifthCyclotomicField :
    CyclicQuinticField ⊓ FifthCyclotomicField = ⊥ :=
  cyclicQuinticField_linearDisjoint_fifthCyclotomicField.inf_eq_bot

/-- The roots-plus-fifth-root compositum has degree twenty. -/
theorem cyclicQuinticCompositum_finrank :
    Module.finrank ℚ
      ((CyclicQuinticField ⊔ FifthCyclotomicField) :
        IntermediateField ℚ Ambient) = 20 := by
  rw [cyclicQuinticField_linearDisjoint_fifthCyclotomicField.finrank_sup,
    cyclicQuinticField_finrank, fifthCyclotomicField_finrank]

/-! ## The unconditional degree obstruction -/

/-- No `ℚ`-algebra embedding of the degree-`20` compositum into the
degree-`10` eleventh-cyclotomic field can exist.  Algebra homomorphisms
between fields are automatically injective, so this is the relevant notion
of field embedding. -/
theorem no_algHom_cyclicQuinticCompositum_to_elevenField :
    ¬ Nonempty
      (((CyclicQuinticField ⊔ FifthCyclotomicField) :
        IntermediateField ℚ Ambient) →ₐ[ℚ] ElevenField) := by
  rintro ⟨f⟩
  letI : FiniteDimensional ℚ ElevenField :=
    IsCyclotomicExtension.finiteDimensional {11} ℚ ElevenField
  have hle := f.toLinearMap.finrank_le_finrank_of_injective f.injective
  rw [cyclicQuinticCompositum_finrank, elevenField_finrank] at hle
  norm_num at hle

/-- In particular, the compositum is not `ℚ`-isomorphic to
`ElevenField`. -/
theorem no_algEquiv_cyclicQuinticCompositum_elevenField :
    ¬ Nonempty
      (((CyclicQuinticField ⊔ FifthCyclotomicField) :
        IntermediateField ℚ Ambient) ≃ₐ[ℚ] ElevenField) := by
  rintro ⟨e⟩
  exact no_algHom_cyclicQuinticCompositum_to_elevenField ⟨e.toAlgHom⟩

/-! ## Conditional interface for the Lazard formula-field bridge

The profile below is intentionally data, not a proposition with an asserted
witness.  Its fields are exactly the information that must ultimately come
from the root-defined Lazard invariants, the branch-correct formula, and the
cyclic Galois action.

The automorphism field is the only part of cyclicity used below.  Requiring a
`ℚ`-automorphism of `E` which fixes `K0` and moves `P1` avoids baking a broad
`IsGalois` instance into the interface.  The downstream root-origin bridge
constructs this automorphism from the concrete cyclic degree-five extension.
-/

/-- A precise conditional interface for the cyclic quintic's one-root
Lazard formula field.

No inhabitant of this structure is supplied in this file. -/
structure CyclicLazardFormulaFieldProfile
    (K0 E : IntermediateField ℚ Ambient) where
  /-- The selected nonzero fifth radical of the formula. -/
  p1 : Ambient
  /-- The formula's square-radical base is contained in `W`. -/
  base_le_fifthCyclotomic : K0 ≤ FifthCyclotomicField
  /-- The square-radical base is contained in the formula field. -/
  base_le_formula : K0 ≤ E
  /-- The formula reconstructs a root, hence contains the cyclic quintic
  field generated by that root. -/
  cyclicQuintic_le_formula : CyclicQuinticField ≤ E
  /-- All selected formula radicals lie in the roots-plus-`zeta5`
  compositum. -/
  formula_le_compositum : E ≤ CyclicQuinticField ⊔ FifthCyclotomicField
  /-- The fifth radical is an element of the formula field. -/
  p1_mem : p1 ∈ E
  /-- Lazard changes branches to ensure this nonvanishing condition. -/
  p1_ne_zero : p1 ≠ 0
  /-- The fifth power of `P1` lies in the square-radical base. -/
  p1_pow_five_mem : p1 ^ 5 ∈ K0
  /-- `P1` generates the formula field over its square-radical base. -/
  formula_eq_base_adjoin : E = K0 ⊔ ℚ⟮p1⟯
  /-- The cyclic degree-five action, restricted to exactly what the Kummer
  ratio argument needs. -/
  conjugation : E ≃ₐ[ℚ] E
  /-- The selected cyclic automorphism fixes the square-radical base. -/
  conjugation_fixes_base :
    ∀ x : K0,
      conjugation
          (⟨(x : Ambient), base_le_formula x.property⟩ : E) =
        (⟨(x : Ambient), base_le_formula x.property⟩ : E)
  /-- The selected nonidentity automorphism moves the generator `P1`. -/
  conjugation_moves_p1 :
    conjugation (⟨p1, p1_mem⟩ : E) ≠ (⟨p1, p1_mem⟩ : E)

namespace CyclicLazardFormulaFieldProfile

variable {K0 E : IntermediateField ℚ Ambient}

/-- `P1`, bundled as an element of the formula field. -/
def p1InFormulaField (P : CyclicLazardFormulaFieldProfile K0 E) : E :=
  ⟨P.p1, P.p1_mem⟩

/-- `P1^5`, bundled as an element of the square-radical base. -/
def p1PowInBaseField (P : CyclicLazardFormulaFieldProfile K0 E) : K0 :=
  ⟨P.p1 ^ 5, P.p1_pow_five_mem⟩

/-- The inclusion into `E` of an element of `K0`. -/
def baseElementInFormulaField
    (P : CyclicLazardFormulaFieldProfile K0 E) (x : K0) : E :=
  ⟨(x : Ambient), P.base_le_formula x.property⟩

/-- The chosen nontrivial conjugate of `P1`. -/
def conjugateP1 (P : CyclicLazardFormulaFieldProfile K0 E) : E :=
  P.conjugation P.p1InFormulaField

/-- The Kummer ratio `sigma(P1)/P1`, as an element of `E`. -/
def fifthRootRatioInFormulaField
    (P : CyclicLazardFormulaFieldProfile K0 E) : E :=
  P.conjugateP1 / P.p1InFormulaField

/-- The same Kummer ratio in the common ambient field. -/
def fifthRootRatio
    (P : CyclicLazardFormulaFieldProfile K0 E) : Ambient :=
  P.fifthRootRatioInFormulaField

theorem p1InFormulaField_ne_zero
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    P.p1InFormulaField ≠ 0 := by
  intro h
  apply P.p1_ne_zero
  exact congrArg Subtype.val h

theorem p1InFormulaField_pow_five_eq_base
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    P.p1InFormulaField ^ 5 =
      P.baseElementInFormulaField P.p1PowInBaseField := by
  apply Subtype.ext
  rfl

/-- Since the automorphism fixes `K0`, the conjugate of `P1` has the same
fifth power as `P1`. -/
theorem conjugateP1_pow_five
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    P.conjugateP1 ^ 5 = P.p1InFormulaField ^ 5 := by
  calc
    P.conjugateP1 ^ 5 =
        P.conjugation (P.p1InFormulaField ^ 5) := by
      rw [conjugateP1, map_pow]
    _ = P.conjugation
        (P.baseElementInFormulaField P.p1PowInBaseField) := by
      rw [P.p1InFormulaField_pow_five_eq_base]
    _ = P.baseElementInFormulaField P.p1PowInBaseField := by
      simpa only [baseElementInFormulaField] using
        P.conjugation_fixes_base P.p1PowInBaseField
    _ = P.p1InFormulaField ^ 5 :=
      P.p1InFormulaField_pow_five_eq_base.symm

theorem fifthRootRatioInFormulaField_pow_five
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    P.fifthRootRatioInFormulaField ^ 5 = 1 := by
  rw [fifthRootRatioInFormulaField, div_pow, P.conjugateP1_pow_five,
    div_self (pow_ne_zero 5 P.p1InFormulaField_ne_zero)]

theorem fifthRootRatioInFormulaField_ne_one
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    P.fifthRootRatioInFormulaField ≠ 1 := by
  intro h
  apply P.conjugation_moves_p1
  simpa only [fifthRootRatioInFormulaField, conjugateP1,
    p1InFormulaField] using
      (div_eq_one_iff_eq P.p1InFormulaField_ne_zero).mp h

/-- A nontrivial ratio of two fifth radicals with the same fifth power is
a primitive fifth root of unity. -/
theorem fifthRootRatioInFormulaField_isPrimitiveRoot
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    IsPrimitiveRoot P.fifthRootRatioInFormulaField 5 := by
  apply isPrimitiveRoot_of_mem_nthRootsFinset Nat.prime_five
  · exact (Polynomial.mem_nthRootsFinset (by norm_num) 1).2
      P.fifthRootRatioInFormulaField_pow_five
  · exact P.fifthRootRatioInFormulaField_ne_one

theorem fifthRootRatio_mem_formula
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    P.fifthRootRatio ∈ E := by
  simpa only [fifthRootRatio] using
    P.fifthRootRatioInFormulaField.property

theorem fifthRootRatio_isPrimitiveRoot
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    IsPrimitiveRoot P.fifthRootRatio 5 := by
  have h := P.fifthRootRatioInFormulaField_isPrimitiveRoot.map_of_injective
    (f := E.val) E.val.injective
  simpa only [fifthRootRatio, IntermediateField.coe_val] using h

/-- The Kummer ratio forces the entire displayed fifth-cyclotomic field
into the one-root formula field. -/
theorem fifthCyclotomicField_le_formula
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    FifthCyclotomicField ≤ E := by
  rw [FifthCyclotomicField, adjoin_simple_le_iff]
  obtain ⟨i, hi, hpow⟩ :=
    P.fifthRootRatio_isPrimitiveRoot.eq_pow_of_pow_eq_one
      zeta5_isPrimitiveRoot.pow_eq_one
  rw [← hpow]
  exact pow_mem P.fifthRootRatio_mem_formula i

/-- The conditional formula facts force the one-root formula field to be
the full degree-`20` compositum `S ⊔ W`. -/
theorem formulaField_eq_cyclicQuinticCompositum
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    E = CyclicQuinticField ⊔ FifthCyclotomicField := by
  apply le_antisymm P.formula_le_compositum
  exact sup_le P.cyclicQuintic_le_formula
    P.fifthCyclotomicField_le_formula

theorem formulaField_finrank
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    Module.finrank ℚ E = 20 := by
  rw [P.formulaField_eq_cyclicQuinticCompositum,
    cyclicQuinticCompositum_finrank]

/-- Once the profile is supplied, the formula field cannot embed into the
literal radical extension `ElevenField`.  This is the degree contradiction
needed for the counterexample to Lazard's Theorem 3. -/
theorem no_algHom_formulaField_to_elevenField
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    ¬ Nonempty (E →ₐ[ℚ] ElevenField) := by
  rw [P.formulaField_eq_cyclicQuinticCompositum]
  exact no_algHom_cyclicQuinticCompositum_to_elevenField

/-- The conditional degree-obstruction package consumed by the downstream
root-origin bridge. -/
theorem theoremThree_degree_obstruction
    (P : CyclicLazardFormulaFieldProfile K0 E) :
    Module.finrank ℚ E = 20 ∧
      ¬ Nonempty (E →ₐ[ℚ] ElevenField) :=
  ⟨P.formulaField_finrank, P.no_algHom_formulaField_to_elevenField⟩

end CyclicLazardFormulaFieldProfile

end

end LeanProofs.PolynomialFormulas.LazardOptimalityTheoremThreeCounterexample
