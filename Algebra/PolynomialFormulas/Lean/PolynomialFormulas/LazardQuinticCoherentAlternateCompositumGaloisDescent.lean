import PolynomialFormulas.LazardQuinticCoherentAlternateGaloisDescent
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Unconditional common-compositum descent for Lazard's alternate formula

The rational theorem in `LazardQuinticCoherentAlternateGaloisDescent` uses
the quintic splitting field itself and therefore asks for a primitive fifth
root in that field.  That excludes, for example, cyclic and dihedral
quintics whose splitting fields need not contain such a root.

Here the ambient field is instead the splitting field of the product of the
quintic and the fifth cyclotomic polynomial.  It contains both ingredients by
construction.  The primitive fifth root, the complete ordered quintic roots,
the rational theta selection, and the finite Galois structure are all derived
inside the proof; none is supplied by the caller.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open IntermediateField
open QuinticScalarGaloisBridge
open QuinticScalarResolventCriterion
open FrobeniusDummitResolvent
open ComputableDummitCoefficients
open LeanProofs.PolynomialFormulas.LazardOptimality

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq α

noncomputable section

/-- A common finite Galois field containing every quintic root and every
primitive fifth root needed by Lazard's Fourier formulas. -/
abbrev QuinticCyclotomicSplittingField (c : DepressedQuintic ℚ) : Type :=
  (c.polynomial * cyclotomic 5 ℚ).SplittingField

/-- An irreducible depressed rational quintic with a rational Lazard
resolvent root has a complete radical reconstruction in the common splitting
field of the quintic and the fifth cyclotomic polynomial.

Unlike the canonical-splitting-field version, this statement has no ambient
field, ordered-root tuple, primitive fifth root, Galois certificate, theta
certificate, or projection-membership premise.  Its returned
`RootTuplePresentation` says directly that the five displayed `d.solve`
values are distinct roots and that every root of the quintic occurs.  The
adjacent `DepressedFiveRootRelations` field is derived from the selected
actual roots and records the stronger multiplicity-sensitive Vieta data. -/
theorem
    exists_commonCompositum_resolventRoot_coherentAlternate_radical_contains_and_reconstructs
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (hq : ∃ q : ℚ, (resolventPolynomial c).IsRoot q) :
    ∃ (x : Fin 5 → QuinticCyclotomicSplittingField c)
        (omega : FifthRootOfUnity (QuinticCyclotomicSplittingField c))
        (d : CoherentAlternateFourierCertificate
          (depressedOfRoots x) (rootInvariants x)),
      Function.Injective x ∧
      elementaryTuple x = depressedElementary
        (c.map (algebraMap ℚ (QuinticCyclotomicSplittingField c))) ∧
      LazardGeneralResolventExplicit.RootTuplePresentation c.polynomial
        (fun k ↦ d.solve omega k) ∧
      DepressedFiveRootRelations
        (c.map (algebraMap ℚ (QuinticCyclotomicSplittingField c)))
        (fun k ↦ d.solve omega k) ∧
      IsRadicalExtension ℚ (QuinticCyclotomicSplittingField c)
          (⊥ : IntermediateField ℚ (QuinticCyclotomicSplittingField c))
          (d.generatedFieldWithRootOfUnity ℚ
            (QuinticCyclotomicSplittingField c)
            (⊥ : IntermediateField ℚ (QuinticCyclotomicSplittingField c))
            omega) ∧
      (∀ k : Fin 5,
        d.solve omega k ∈
          d.generatedFieldWithRootOfUnity ℚ
            (QuinticCyclotomicSplittingField c)
            (⊥ : IntermediateField ℚ (QuinticCyclotomicSplittingField c))
            omega) ∧
      (fun k ↦ d.solve omega k) =
        reversedRootTuple
          (rootsForBranch x
            (correctedQuadraticBranch
              (depressedOfRoots x) (rootInvariants x)
              (rootQuadraticTriple omega x))) := by
  let K := QuinticCyclotomicSplittingField c
  let productPolynomial : ℚ[X] := c.polynomial * cyclotomic 5 ℚ
  have hproduct : productPolynomial ≠ 0 := by
    exact mul_ne_zero hp.ne_zero (cyclotomic_ne_zero 5 ℚ)
  letI : DecidableEq K := Classical.decEq K
  letI : productPolynomial.IsSplittingField ℚ K := by
    exact Polynomial.IsSplittingField.splittingField productPolynomial
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K productPolynomial

  have hnotdvd : ¬c.polynomial ∣ cyclotomic 5 ℚ := by
    apply c.polynomial_monic.not_dvd_of_natDegree_lt
      (cyclotomic_ne_zero 5 ℚ)
    rw [c.polynomial_natDegree, natDegree_cyclotomic]
    norm_num [Nat.totient]
    decide
  have hcoprime : IsCoprime c.polynomial (cyclotomic 5 ℚ) :=
    hp.coprime_iff_not_dvd.mpr hnotdvd
  have hseparable : productPolynomial.Separable := by
    exact hp.separable.mul (separable_cyclotomic 5 ℚ) hcoprime
  letI : IsGalois ℚ K :=
    IsGalois.of_separable_splitting_field hseparable

  have hquinticSplits :
      (c.polynomial.map (algebraMap ℚ K)).Splits := by
    exact (SplittingField.splits productPolynomial).of_dvd
      (map_ne_zero hproduct)
      ((map_dvd_map' _).mpr
        (show c.polynomial ∣ productPolynomial from
          dvd_mul_right c.polynomial (cyclotomic 5 ℚ)))
  letI : Fact ((c.polynomial.map (algebraMap ℚ K)).Splits) :=
    ⟨hquinticSplits⟩

  have hcyclotomicSplits :
      ((cyclotomic 5 ℚ).map (algebraMap ℚ K)).Splits := by
    exact (SplittingField.splits productPolynomial).of_dvd
      (map_ne_zero hproduct)
      ((map_dvd_map' _).mpr
        (show cyclotomic 5 ℚ ∣ productPolynomial from
          dvd_mul_left (cyclotomic 5 ℚ) c.polynomial))
  obtain ⟨zeta, hzeta⟩ :=
    hcyclotomicSplits.exists_eval_eq_zero (by
      rw [degree_map]
      exact degree_ne_of_natDegree_ne (by
        rw [natDegree_cyclotomic]
        norm_num))
  have hzetaRoot : (cyclotomic 5 K).IsRoot zeta := by
    rw [IsRoot.def, ← map_cyclotomic 5 (algebraMap ℚ K)]
    exact hzeta
  have hzetaPrimitive : IsPrimitiveRoot zeta 5 :=
    (isRoot_cyclotomic_iff).mp hzetaRoot
  let omega : FifthRootOfUnity K := ⟨zeta, hzetaPrimitive⟩

  let canonicalRoots : Fin 5 → c.polynomial.SplittingField :=
    rootTuple c.polynomial hp c.polynomial_natDegree
  let phi : c.polynomial.SplittingField →+* K :=
    algebraMap c.polynomial.SplittingField K
  let roots : Fin 5 → K := fun k ↦ phi (canonicalRoots k)
  let commonRootEquiv : Fin 5 ≃ c.polynomial.rootSet K :=
    (rootEquiv c.polynomial hp c.polynomial_natDegree).symm.trans
      (Polynomial.Gal.rootsEquivRoots c.polynomial K)
  have hcommonRootEquiv (k : Fin 5) :
      (commonRootEquiv k : K) = roots k := by
    rfl
  have presentation :
      LazardGeneralResolventExplicit.RootTuplePresentation c.polynomial roots := by
    refine
      { splits := hquinticSplits
        nodup := phi.injective.comp
          (rootTuple_injective c.polynomial hp c.polynomial_natDegree)
        complete := ?_ }
    intro y
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := commonRootEquiv.surjective ⟨y, hy⟩
      refine ⟨k, ?_⟩
      calc
        roots k = (commonRootEquiv k : K) := (hcommonRootEquiv k).symm
        _ = y := congrArg Subtype.val hk
    · rintro ⟨k, rfl⟩
      rw [← hcommonRootEquiv k]
      exact (commonRootEquiv k).property

  have reindexPresentation
      (y : Fin 5 → K)
      (hy : LazardGeneralResolventExplicit.RootTuplePresentation c.polynomial y)
      (e : Equiv.Perm (Fin 5)) :
      LazardGeneralResolventExplicit.RootTuplePresentation c.polynomial
        (fun k ↦ y (e k)) := by
    refine
      { splits := hy.splits
        nodup := hy.nodup.comp e.injective
        complete := ?_ }
    intro z
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := (hy.complete z).1 hz
      refine ⟨e.symm k, ?_⟩
      simpa using hk
    · rintro ⟨k, rfl⟩
      exact (hy.complete _).2 ⟨e k, rfl⟩

  have hthetaMap (j : Fin 6) :
      phi (thetaValue canonicalRoots j) = thetaValue roots j := by
    exact map_thetaValue_of_maps_roots phi canonicalRoots roots 1 j j
      (by intro k; simp [roots]) (by simp)
  have hthetaInjective : Function.Injective (thetaValue roots) := by
    intro i j hij
    apply thetaValue_rootTuple_injective
      c.polynomial hp c.polynomial_natDegree
    exact phi.injective
      ((hthetaMap i).trans (hij.trans (hthetaMap j).symm))

  obtain ⟨q, hq⟩ := hq
  have hqCanonical := Polynomial.IsRoot.map
    (f := algebraMap ℚ c.polynomial.SplittingField) hq
  rw [resolventPolynomial_map_eq_scalarResolvent_rootTuple c hp]
    at hqCanonical
  obtain ⟨i, hi⟩ :=
    (scalarResolvent_isRoot_iff canonicalRoots
      (algebraMap ℚ c.polynomial.SplittingField q)).mp hqCanonical
  have hthetaBase : ∃ q : ℚ, algebraMap ℚ K q = thetaValue roots i := by
    refine ⟨q, ?_⟩
    calc
      algebraMap ℚ K q =
          phi (algebraMap ℚ c.polynomial.SplittingField q) := by
        rw [IsScalarTower.algebraMap_apply ℚ
          c.polynomial.SplittingField K]
      _ = phi (thetaValue canonicalRoots i) := congrArg phi hi.symm
      _ = thetaValue roots i := hthetaMap i

  have helementaryRoots :
      elementaryTuple roots =
        depressedElementary (c.map (algebraMap ℚ K)) := by
    calc
      elementaryTuple roots =
          fun k ↦ phi (elementaryTuple canonicalRoots k) := by
        simpa [roots] using elementaryTuple_map phi canonicalRoots
      _ = fun k ↦ phi
          (depressedElementary
            (c.map (algebraMap ℚ c.polynomial.SplittingField)) k) := by
        rw [show elementaryTuple canonicalRoots =
            depressedElementary
              (c.map (algebraMap ℚ c.polynomial.SplittingField)) by
          simpa [canonicalRoots] using
            elementaryTuple_rootTuple_eq_depressedElementary c hp]
      _ = depressedElementary (c.map (algebraMap ℚ K)) := by
        funext k
        fin_cases k <;>
          simp [depressedElementary, DepressedQuintic.map, phi]

  let x : Fin 5 → K := selectedCommonRootTuple roots i
  have hx : Function.Injective x :=
    presentation.nodup.comp
      (FrobeniusDummitResolvent.representative i).injective
  have helementary :
      elementaryTuple x =
        depressedElementary (c.map (algebraMap ℚ K)) := by
    have hselected : x = fun k ↦ roots
        (FrobeniusDummitResolvent.representative i k) := by
      rfl
    calc
      elementaryTuple x = elementaryTuple roots := by
        rw [hselected]
        exact elementaryTuple_representative roots i
      _ = depressedElementary (c.map (algebraMap ℚ K)) :=
        helementaryRoots
  have presentationX :
      LazardGeneralResolventExplicit.RootTuplePresentation c.polynomial x := by
    have hselected : x = fun k ↦ roots
        (FrobeniusDummitResolvent.representative i k) := by
      rfl
    rw [hselected]
    exact reindexPresentation roots presentation
      (FrobeniusDummitResolvent.representative i)
  have hsum : elementaryTuple x 0 = 0 := by
    rw [helementary]
    simp [depressedElementary]
  have hc : depressedOfRoots x = c.map (algebraMap ℚ K) :=
    depressedOfRoots_eq_of_elementaryTuple_eq
      (c.map (algebraMap ℚ K)) x helementary
  have hepsilon : rootEpsilon omega x ≠ 0 :=
    rootEpsilon_ne_zero_of_elementaryTuple_eq c hp x helementary omega
  let d := rootCoherentAlternateFourierCertificate
    omega x hsum hx hepsilon
  have htower :=
    selectedCommonRootTuple_radical_contains_and_reconstructs_of_depressed_base
      c roots presentation i hthetaBase hthetaInjective omega hc hsum
        (invariantSystemMatrix_det_ne_zero c hp) hepsilon
  have htower' :
      IsRadicalExtension ℚ K (⊥ : IntermediateField ℚ K)
          (d.generatedFieldWithRootOfUnity ℚ K
            (⊥ : IntermediateField ℚ K) omega) ∧
        (∀ k : Fin 5,
          d.solve omega k ∈
            d.generatedFieldWithRootOfUnity ℚ K
              (⊥ : IntermediateField ℚ K) omega) ∧
        (fun k ↦ d.solve omega k) =
          reversedRootTuple
            (rootsForBranch x
              (correctedQuadraticBranch
                (depressedOfRoots x) (rootInvariants x)
                (rootQuadraticTriple omega x))) := by
    simpa [x, d] using htower
  have hsolve := htower'.2.2

  let branch := correctedQuadraticBranch
    (depressedOfRoots x) (rootInvariants x) (rootQuadraticTriple omega x)
  let branchRoots : Fin 5 → K := rootsForBranch x branch
  have presentationBranch :
      LazardGeneralResolventExplicit.RootTuplePresentation c.polynomial
        branchRoots := by
    have hbranch : branchRoots = fun k ↦ x
        ((multiplierTwo ^ branchMultiplierExponent branch) k) := by
      rfl
    rw [hbranch]
    exact reindexPresentation x presentationX
      (multiplierTwo ^ branchMultiplierExponent branch)
  let reversal : Equiv.Perm (Fin 5) :=
    { toFun := ![0, 4, 3, 2, 1]
      invFun := ![0, 4, 3, 2, 1]
      left_inv := by intro k; fin_cases k <;> rfl
      right_inv := by intro k; fin_cases k <;> rfl }
  have hreversal :
      reversedRootTuple branchRoots = fun k ↦ branchRoots (reversal k) := by
    funext k
    fin_cases k <;> rfl
  have presentationReversed :
      LazardGeneralResolventExplicit.RootTuplePresentation c.polynomial
        (reversedRootTuple branchRoots) := by
    rw [hreversal]
    exact reindexPresentation branchRoots presentationBranch reversal
  have hsolve' :
      (fun k ↦ d.solve omega k) = reversedRootTuple branchRoots := by
    simpa [branch, branchRoots] using hsolve
  have presentationSolve :
      LazardGeneralResolventExplicit.RootTuplePresentation c.polynomial
        (fun k ↦ d.solve omega k) := by
    rw [hsolve']
    exact presentationReversed
  have hrelationsSolve :
      DepressedFiveRootRelations (c.map (algebraMap ℚ K))
        (fun k ↦ d.solve omega k) := by
    rw [hsolve']
    simpa [hc] using
      depressedFiveRootRelations_reversed_rootsForBranch x hsum branch
  exact ⟨x, omega, d, hx, helementary, presentationSolve,
    hrelationsSolve, htower'.1, htower'.2.1, hsolve⟩

end

end LeanProofs.PolynomialFormulas.LazardQuintic
