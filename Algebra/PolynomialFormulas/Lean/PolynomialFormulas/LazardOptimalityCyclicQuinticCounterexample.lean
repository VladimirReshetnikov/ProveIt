import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PolynomialFormulas.LazardOptimalityCyclotomicCounterexample

/-!
# A cyclic quintic counterexample to Lazard's Theorem 4 as stated

Let `z` be a primitive eleventh root of unity and put `x = z + z⁻¹`.
The polynomial

`X⁵ + X⁴ - 4X³ - 3X² + 3X + 1`

is irreducible over `ℚ`, has `x` as a root, and splits in the eleventh
cyclotomic field.  That field is a one-step radical extension according to
Lazard's literal Definition 1, but it omits the primitive fifth root in the
common `55`th-cyclotomic ambient field.

Thus this file upgrades the cyclotomic obstruction from the preceding file
to the actual irreducible-quintic/all-roots hypotheses of Theorem 4.
-/

namespace LeanProofs.PolynomialFormulas.LazardOptimalityCyclicQuinticCounterexample

open Polynomial
open IntermediateField
open LeanProofs.PolynomialFormulas.LazardOptimality
open LeanProofs.PolynomialFormulas.LazardOptimalityCyclotomicCounterexample

set_option autoImplicit false

/-- The integer cyclic quintic for `zeta11 + zeta11⁻¹`. -/
noncomputable def cyclicQuinticZ : ℤ[X] :=
  X ^ 5 + X ^ 4 - C 4 * X ^ 3 - C 3 * X ^ 2 + C 3 * X + C 1

/-- Its translate by `X ↦ X + 2`; this is Eisenstein at `11`. -/
noncomputable def shiftedCyclicQuinticZ : ℤ[X] :=
  X ^ 5 + C 11 * X ^ 4 + C 44 * X ^ 3 + C 77 * X ^ 2 + C 55 * X + C 11

/-- The same quintic over `ℚ`. -/
noncomputable def cyclicQuinticQ : ℚ[X] :=
  cyclicQuinticZ.map (algebraMap ℤ ℚ)

theorem cyclicQuinticZ_monic : cyclicQuinticZ.Monic := by
  simp only [cyclicQuinticZ]
  monicity!

theorem cyclicQuinticZ_natDegree : cyclicQuinticZ.natDegree = 5 := by
  simp only [cyclicQuinticZ]
  compute_degree!

theorem shiftedCyclicQuinticZ_monic : shiftedCyclicQuinticZ.Monic := by
  simp only [shiftedCyclicQuinticZ]
  monicity!

theorem shiftedCyclicQuinticZ_natDegree :
    shiftedCyclicQuinticZ.natDegree = 5 := by
  simp only [shiftedCyclicQuinticZ]
  compute_degree!

/-- The elementary translate identity exposing Eisenstein's criterion. -/
theorem cyclicQuinticZ_comp_X_add_two :
    cyclicQuinticZ.comp (X + C 2) = shiftedCyclicQuinticZ := by
  simp [cyclicQuinticZ, shiftedCyclicQuinticZ] <;> ring

local notation "P11" => Ideal.span ({(11 : ℤ)} : Set ℤ)

theorem elevenIdeal_isPrime : (P11 : Ideal ℤ).IsPrime := by
  exact (Ideal.span_singleton_prime (by norm_num : (11 : ℤ) ≠ 0)).2 (by decide)

theorem shiftedCyclicQuinticZ_isEisensteinAt :
    shiftedCyclicQuinticZ.IsEisensteinAt P11 := by
  refine shiftedCyclicQuinticZ_monic.isEisensteinAt_of_mem_of_notMem
    elevenIdeal_isPrime.ne_top ?_ ?_
  · intro n hn
    rw [shiftedCyclicQuinticZ_natDegree] at hn
    interval_cases n <;>
      simp [shiftedCyclicQuinticZ, Polynomial.coeff_X,
        Ideal.mem_span_singleton]
  · rw [show shiftedCyclicQuinticZ.coeff 0 = 11 by
          norm_num [shiftedCyclicQuinticZ],
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num

theorem shiftedCyclicQuinticZ_irreducible :
    Irreducible shiftedCyclicQuinticZ :=
  shiftedCyclicQuinticZ_isEisensteinAt.irreducible elevenIdeal_isPrime
    shiftedCyclicQuinticZ_monic.isPrimitive
    (by rw [shiftedCyclicQuinticZ_natDegree]; norm_num)

/-- Translation is a polynomial-algebra automorphism, so irreducibility of
the Eisenstein translate implies irreducibility of the original quintic. -/
theorem cyclicQuinticZ_irreducible : Irreducible cyclicQuinticZ := by
  have himage :
      Irreducible ((Polynomial.algEquivAevalXAddC (2 : ℤ)) cyclicQuinticZ) := by
    simpa only [Polynomial.algEquivAevalXAddC_apply,
      ← Polynomial.comp_eq_aeval, cyclicQuinticZ_comp_X_add_two] using
        shiftedCyclicQuinticZ_irreducible
  exact (MulEquiv.irreducible_iff
    (Polynomial.algEquivAevalXAddC (2 : ℤ))).mp himage

theorem cyclicQuinticQ_monic : cyclicQuinticQ.Monic := by
  simpa only [cyclicQuinticQ] using
    cyclicQuinticZ_monic.map (algebraMap ℤ ℚ)

theorem cyclicQuinticQ_natDegree : cyclicQuinticQ.natDegree = 5 := by
  rw [cyclicQuinticQ, cyclicQuinticZ_monic.natDegree_map,
    cyclicQuinticZ_natDegree]

theorem cyclicQuinticQ_irreducible : Irreducible cyclicQuinticQ := by
  exact (cyclicQuinticZ_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp cyclicQuinticZ_irreducible

/-! ## The cyclotomic root and the Laurent-polynomial identity -/

/-- The chosen primitive eleventh root, regarded as an element of the
eleventh-cyclotomic intermediate field. -/
noncomputable def zeta11InElevenField : ElevenField :=
  ⟨zeta11, by
    rw [ElevenField]
    exact mem_adjoin_simple_self ℚ zeta11⟩

theorem zeta11InElevenField_isPrimitiveRoot :
    IsPrimitiveRoot zeta11InElevenField 11 := by
  apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
  simpa only [zeta11InElevenField] using zeta11_isPrimitiveRoot

/-- The real-cyclotomic generator whose conjugates give the five roots. -/
noncomputable def cyclicQuinticRoot : ElevenField :=
  zeta11InElevenField + zeta11InElevenField⁻¹

/-- Evaluation of the mapped integer polynomial has the expected explicit
coefficient expression in every `ℚ`-algebra field. -/
theorem aeval_cyclicQuinticQ
    (K : Type*) [Field K] [Algebra ℚ K] (x : K) :
    aeval x cyclicQuinticQ =
      x ^ 5 + x ^ 4 - 4 * x ^ 3 - 3 * x ^ 2 + 3 * x + 1 := by
  simp only [cyclicQuinticQ, cyclicQuinticZ, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_ofNat,
    Polynomial.map_one, Polynomial.aeval_add, Polynomial.aeval_sub,
    Polynomial.aeval_mul, map_pow, Polynomial.aeval_X,
    map_ofNat, map_one]

/-- The Laurent identity behind the explicit cyclic quintic. -/
theorem scaled_cyclicQuintic_identity
    (K : Type*) [Field K] (z : K) (hz : z ≠ 0) :
    z ^ 5 *
        ((z + z⁻¹) ^ 5 + (z + z⁻¹) ^ 4 - 4 * (z + z⁻¹) ^ 3 -
          3 * (z + z⁻¹) ^ 2 + 3 * (z + z⁻¹) + 1) =
      ∑ j ∈ Finset.range 11, z ^ j := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  field_simp [hz]
  ring

theorem cyclicQuinticRoot_isRoot :
    aeval cyclicQuinticRoot cyclicQuinticQ = 0 := by
  let z : ElevenField := zeta11InElevenField
  have hz0 : z ≠ 0 :=
    zeta11InElevenField_isPrimitiveRoot.ne_zero (by norm_num)
  have hgeom : ∑ j ∈ Finset.range 11, z ^ j = 0 :=
    zeta11InElevenField_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  have hscaled : z ^ 5 * aeval cyclicQuinticRoot cyclicQuinticQ =
      ∑ j ∈ Finset.range 11, z ^ j := by
    rw [aeval_cyclicQuinticQ]
    simpa only [cyclicQuinticRoot, z] using
      scaled_cyclicQuintic_identity ElevenField z hz0
  have hzero : z ^ 5 * aeval cyclicQuinticRoot cyclicQuinticQ = 0 :=
    hscaled.trans hgeom
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 5 hz0)

theorem cyclicQuinticQ_eq_minpoly :
    cyclicQuinticQ = minpoly ℚ cyclicQuinticRoot :=
  minpoly.eq_of_irreducible_of_monic cyclicQuinticQ_irreducible
    cyclicQuinticRoot_isRoot cyclicQuinticQ_monic

/-! ## Every root lies in the radical `11`th-cyclotomic subfield -/

theorem cyclicQuinticQ_splits_elevenField :
    (cyclicQuinticQ.map (algebraMap ℚ ElevenField)).Splits := by
  letI : IsGalois ℚ ElevenField :=
    IsCyclotomicExtension.isGalois {11} ℚ ElevenField
  have h := IsGalois.splits ℚ cyclicQuinticRoot
  simpa only [cyclicQuinticQ_eq_minpoly] using h

theorem cyclicQuinticQ_splits_ambient :
    (cyclicQuinticQ.map (algebraMap ℚ Ambient)).Splits := by
  have h := cyclicQuinticQ_splits_elevenField.map
    (algebraMap ElevenField Ambient)
  simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using h

/-- Every root in the common ambient field belongs to the competing radical
extension `ElevenField`. -/
theorem cyclicQuinticQ_rootSet_subset_elevenField :
    cyclicQuinticQ.rootSet Ambient ⊆ ElevenField := by
  exact (IntermediateField.splits_iff_mem
    (F := ElevenField) cyclicQuinticQ_splits_ambient).mp
      cyclicQuinticQ_splits_elevenField

/-- The field claimed in Lazard's Theorem 4 (roots together with a primitive
fifth root) is not even contained in this competing radical field. -/
theorem claimedField_not_le_elevenField :
    ¬ generatedWithRootOfUnity ℚ Ambient
        (cyclicQuinticQ.rootSet Ambient) zeta5 ≤ ElevenField := by
  intro hle
  exact zeta5_not_mem_elevenField
    (hle (rootOfUnity_mem_generatedWithRootOfUnity ℚ Ambient
      (cyclicQuinticQ.rootSet Ambient) zeta5))

/-- The unconditional forcing premise needed by the abstract leastness
lemma is itself false for this quintic. -/
theorem primitiveFifthRoot_isNotForcedByRadicality :
    ¬ ∀ L : IntermediateField ℚ Ambient,
      IsRadicalExtension ℚ Ambient
          (⊥ : IntermediateField ℚ Ambient) L →
        cyclicQuinticQ.rootSet Ambient ⊆ L → zeta5 ∈ L := by
  intro hforced
  exact zeta5_not_mem_elevenField
    (hforced ElevenField elevenField_isRadicalExtension
      cyclicQuinticQ_rootSet_subset_elevenField)

/-- Consequently the roots-plus-`zeta5` field cannot satisfy the literal
leastness conclusion of Lazard's Theorem 4. -/
theorem claimedField_isNotLeastRadicalExtensionContaining :
    ¬ IsLeastRadicalExtensionContaining ℚ Ambient
      (⊥ : IntermediateField ℚ Ambient)
      (generatedWithRootOfUnity ℚ Ambient
        (cyclicQuinticQ.rootSet Ambient) zeta5)
      (cyclicQuinticQ.rootSet Ambient) := by
  exact not_isLeastRadicalExtensionContaining_of_competing_missing
    ℚ Ambient elevenField_isRadicalExtension
      cyclicQuinticQ_rootSet_subset_elevenField
      (rootOfUnity_mem_generatedWithRootOfUnity ℚ Ambient
        (cyclicQuinticQ.rootSet Ambient) zeta5)
      zeta5_not_mem_elevenField

/-- The full formal counterexample package: an irreducible quintic that
splits in a literal radical extension, while that extension omits the
primitive fifth root present in the ambient field. -/
theorem lazard_theorem4_counterexample :
    cyclicQuinticQ.Monic ∧
      cyclicQuinticQ.natDegree = 5 ∧
      Irreducible cyclicQuinticQ ∧
      (cyclicQuinticQ.map (algebraMap ℚ Ambient)).Splits ∧
      cyclicQuinticQ.rootSet Ambient ⊆ ElevenField ∧
      IsRadicalExtension ℚ Ambient
        (⊥ : IntermediateField ℚ Ambient) ElevenField ∧
      IsPrimitiveRoot zeta5 5 ∧
      zeta5 ∉ ElevenField ∧
      (¬ ∀ L : IntermediateField ℚ Ambient,
        IsRadicalExtension ℚ Ambient
            (⊥ : IntermediateField ℚ Ambient) L →
          cyclicQuinticQ.rootSet Ambient ⊆ L → zeta5 ∈ L) ∧
      ¬ IsLeastRadicalExtensionContaining ℚ Ambient
        (⊥ : IntermediateField ℚ Ambient)
        (generatedWithRootOfUnity ℚ Ambient
          (cyclicQuinticQ.rootSet Ambient) zeta5)
        (cyclicQuinticQ.rootSet Ambient) :=
  ⟨cyclicQuinticQ_monic, cyclicQuinticQ_natDegree,
    cyclicQuinticQ_irreducible, cyclicQuinticQ_splits_ambient,
    cyclicQuinticQ_rootSet_subset_elevenField,
    elevenField_isRadicalExtension, zeta5_isPrimitiveRoot,
    zeta5_not_mem_elevenField,
    primitiveFifthRoot_isNotForcedByRadicality,
    claimedField_isNotLeastRadicalExtensionContaining⟩

end LeanProofs.PolynomialFormulas.LazardOptimalityCyclicQuinticCounterexample
