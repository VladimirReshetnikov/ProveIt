import PolynomialFormulas.LazardQuinticCoherentAlternateCompositumGaloisDescent
import PolynomialFormulas.LazardQuinticGeneralSolvabilityTransport

/-!
# General rational endpoint for the denominator-safe Lazard formula

This file translates the coherent-alternate common-compositum construction
back from the depressed monic quintic to an arbitrary irreducible rational
quintic with nonzero leading coefficient.  Unlike the older standard-formula
wrapper, this path never invokes a theorem requiring `invariantE ≠ 0`.

The returned values are definitionally the five coherent-alternate
inverse-Fourier outputs minus the rational Tschirnhaus shift.  Their Vieta
relations, exact factorization, soundness, and exhaustion are derived from
the actual root-origin relation returned by the common-compositum theorem;
none is a caller-supplied certificate.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open Polynomial IntermediateField
open LeanProofs.PolynomialFormulas.LazardOptimality
open ComputableDummitCoefficients

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq α

noncomputable section

/-- Common splitting field used by the denominator-safe formula for the
depressed translate of a general rational quintic. -/
abbrev GeneralQuinticCyclotomicSplittingField
    (c : GeneralQuintic ℚ) : Type :=
  QuinticCyclotomicSplittingField (depress c)

/-- A general irreducible rational quintic with a rational Lazard-resolvent
root has five explicit coherent-alternate outputs in one radical field.
They are pairwise distinct, give the exact leading-coefficient-scaled
linear-factor product, and exhaust the root set. -/
theorem
    exists_general_commonCompositum_coherentAlternate_completeRootVector
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial)
    (hq : ∃ q : ℚ, (resolventPolynomial (depress c)).IsRoot q) :
    ∃ (x : Fin 5 → GeneralQuinticCyclotomicSplittingField c)
        (omega : FifthRootOfUnity
          (GeneralQuinticCyclotomicSplittingField c))
        (d : CoherentAlternateFourierCertificate
          (depressedOfRoots x) (rootInvariants x)),
      let K := GeneralQuinticCyclotomicSplittingField c
      let phi := algebraMap ℚ K
      let shift := phi (depressionShift c)
      let roots := fun k : Fin 5 ↦ d.solve omega k - shift
      let L := d.generatedFieldWithRootOfUnity ℚ K
        (⊥ : IntermediateField ℚ K) omega
      IsRadicalExtension ℚ K (⊥ : IntermediateField ℚ K) L ∧
        (∀ k : Fin 5, roots k ∈ L) ∧
        Function.Injective roots ∧
        ((c.map phi).polynomial =
          Polynomial.C (phi c.a) *
            ∏ k : Fin 5, (Polynomial.X - Polynomial.C (roots k))) ∧
        (∀ z : K, (c.map phi).eval z = 0 ↔
          ∃ k : Fin 5, z = roots k) := by
  have hpdep : Irreducible (depress c).polynomial :=
    (irreducible_polynomial_iff_depress_polynomial c ha).mp hp
  obtain ⟨x, omega, d, _hx, _helementary, hpresentation, hrelations,
      hradical, hmem, _hsolve⟩ :=
    exists_commonCompositum_resolventRoot_coherentAlternate_radical_contains_and_reconstructs
      (depress c) hpdep hq
  refine ⟨x, omega, d, ?_⟩
  let K := GeneralQuinticCyclotomicSplittingField c
  let phi : ℚ →+* K := algebraMap ℚ K
  let shift : K := phi (depressionShift c)
  let roots : Fin 5 → K := fun k ↦ d.solve omega k - shift
  let L : IntermediateField ℚ K :=
    d.generatedFieldWithRootOfUnity ℚ K
      (⊥ : IntermediateField ℚ K) omega
  have haK : (c.map phi).a ≠ 0 := by
    simpa [GeneralQuintic.map] using
      (map_ne_zero_iff phi phi.injective).2 ha
  have hrelations' :
      DepressedFiveRootRelations (depress (c.map phi))
        (fun k ↦ d.solve omega k) := by
    rw [depress_map]
    simpa [K, phi] using hrelations
  have hgeneral : FiveRootRelations (c.map phi) roots := by
    simpa [roots, shift, depressionShift, GeneralQuintic.map] using
      hrelations'.translate (c.map phi) haK
  have hshiftmem : shift ∈ L := by
    exact L.algebraMap_mem (depressionShift c)
  refine ⟨?_, ?_, ?_, hgeneral.factorization, ?_⟩
  · simpa [K, L] using hradical
  · intro k
    exact sub_mem (by simpa [K, L] using hmem k) hshiftmem
  · intro i j hij
    have hsub : d.solve omega i - shift = d.solve omega j - shift := by
      simpa [roots] using hij
    apply hpresentation.nodup
    exact sub_left_injective hsub
  · intro z
    constructor
    · exact hgeneral.exists_eq_of_eval_eq_zero haK
    · rintro ⟨k, rfl⟩
      change (c.map phi).eval (roots k) = 0
      rw [hgeneral.eval_factorization]
      exact mul_eq_zero.mpr (Or.inr
        (Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)))

/-- Fully semantic general-rational endpoint.  Complete radical solvability
of the original polynomial supplies the resolvent root, after which the
preceding theorem uses only the coherent-alternate denominator-safe path. -/
theorem
    exists_general_commonCompositum_coherentAlternate_completeRootVector_of_completelySolvableByRadicals
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial)
    (hsolvable : CompletelySolvableByRadicals c.polynomial) :
    ∃ (x : Fin 5 → GeneralQuinticCyclotomicSplittingField c)
        (omega : FifthRootOfUnity
          (GeneralQuinticCyclotomicSplittingField c))
        (d : CoherentAlternateFourierCertificate
          (depressedOfRoots x) (rootInvariants x)),
      let K := GeneralQuinticCyclotomicSplittingField c
      let phi := algebraMap ℚ K
      let shift := phi (depressionShift c)
      let roots := fun k : Fin 5 ↦ d.solve omega k - shift
      let L := d.generatedFieldWithRootOfUnity ℚ K
        (⊥ : IntermediateField ℚ K) omega
      IsRadicalExtension ℚ K (⊥ : IntermediateField ℚ K) L ∧
        (∀ k : Fin 5, roots k ∈ L) ∧
        Function.Injective roots ∧
        ((c.map phi).polynomial =
          Polynomial.C (phi c.a) *
            ∏ k : Fin 5, (Polynomial.X - Polynomial.C (roots k))) ∧
        (∀ z : K, (c.map phi).eval z = 0 ↔
          ∃ k : Fin 5, z = roots k) := by
  apply exists_general_commonCompositum_coherentAlternate_completeRootVector
    c ha hp
  exact exists_depressed_resolvent_root_of_completelySolvableByRadicals
    c ha hp hsolvable

end

end LeanProofs.PolynomialFormulas.LazardQuintic
