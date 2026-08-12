import PolynomialFormulas.LazardQuinticCoherentAlternateRadicalTower
import PolynomialFormulas.LazardQuinticGeneralSolvabilityTransport

/-!
# Conditional general-quintic adapter for the denominator-safe alternate path

The common-compositum descent is a separate construction: it supplies an
ordered root tuple, a primitive fifth root, and the descended invariant and
projection data.  This file isolates the algebraic adapter after those data
are available.  It translates the denominator-safe alternate reconstruction
through general-quintic depression and proves the exact factorization and
root-set theorem without assuming Lazard's standard denominator `E` is
nonzero.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open IntermediateField
open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients
open LeanProofs.PolynomialFormulas.LazardOptimality

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

theorem exists_coherentAlternate_general_rootVector_of_data
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    [Algebra ℚ K]
    (B : IntermediateField ℚ K)
    (x : Fin 5 → K)
    (omega : FifthRootOfUnity K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0)
    (hdata : RadicalInvariantDataIn ℚ K B
      (depressedOfRoots x) (rootInvariants x))
    (hprojections : ∀ j,
      rootCoherentAlternateProjectionValues omega x j ∈ B)
    (homega : IsRadicalExtension ℚ K B ℚ⟮omega.value⟯)
    (hdepressed : depressedOfRoots x =
      (depress c).map (algebraMap ℚ K)) :
    ∃ (roots : Fin 5 → K) (L : IntermediateField ℚ K),
      IsRadicalExtension ℚ K B L ∧
      (∀ k : Fin 5, roots k ∈ L) ∧
      Function.Injective roots ∧
      ((c.map (algebraMap ℚ K)).polynomial =
        Polynomial.C ((algebraMap ℚ K) c.a) *
          ∏ k : Fin 5, (Polynomial.X - Polynomial.C (roots k))) ∧
      (∀ z : K,
        (c.map (algebraMap ℚ K)).eval z = 0 ↔
          ∃ k : Fin 5, z = roots k) := by
  let d := rootCoherentAlternateFourierCertificate
    omega x hsum hinjective hepsilon
  let L := d.generatedFieldWithRootOfUnity ℚ K B omega
  have hd := rootCoherentAlternate_radical_contains_and_reconstructs
    (F := ℚ) (K := K) B omega x hsum hinjective hepsilon hdata
      hprojections homega
  have hsolve : (fun k => d.solve omega k) =
      reversedRootTuple
        (rootsForBranch x
          (correctedQuadraticBranch
            (depressedOfRoots x) (rootInvariants x)
            (rootQuadraticTriple omega x))) := by
    exact hd.2.2
  have hsolve_injective : Function.Injective (fun k => d.solve omega k) := by
    rw [hsolve]
    exact reversedRootTuple_injective
      (permuteRootTuple_injective hinjective _)
  let phi : ℚ →+* K := algebraMap ℚ K
  let shift : K := phi (depressionShift c)
  let roots : Fin 5 → K := fun k => d.solve omega k - shift
  have haK : (c.map phi).a ≠ 0 := by
    simpa [GeneralQuintic.map] using
      (map_ne_zero_iff phi phi.injective).2 ha
  have hdepressed' : depressedOfRoots x =
      depress (c.map phi) := by
    rw [depress_map]
    exact hdepressed
  have hdep : DepressedFiveRootRelations
      (depress (c.map phi)) (fun k => d.solve omega k) := by
    rw [← hdepressed']
    exact rootCoherentAlternateFourierCertificate_fiveRootRelations
      omega x hsum hinjective hepsilon
  have hgeneral : FiveRootRelations (c.map phi) roots := by
    simpa [roots, shift, depressionShift, GeneralQuintic.map] using
      hdep.translate (c.map phi) haK
  refine ⟨roots, L, ?_, ?_, ?_, hgeneral.factorization, ?_⟩
  · simpa [L] using hd.1
  · intro k
    exact sub_mem (by simpa [L] using hd.2.1 k)
      (L.algebraMap_mem (depressionShift c))
  · intro i j hij
    apply hsolve_injective
    apply sub_left_injective (b := shift)
    simpa [roots] using hij
  · intro z
    constructor
    · exact hgeneral.exists_eq_of_eval_eq_zero haK
    · rintro ⟨k, rfl⟩
      rw [hgeneral.eval_factorization]
      apply mul_eq_zero_of_right
      exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)

end

end LeanProofs.PolynomialFormulas.LazardQuintic
