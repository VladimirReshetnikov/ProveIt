import PolynomialFormulas.LazardInvariantModularCyclicDegreeSevenReconstruction
import PolynomialFormulas.LazardInvariantModularCyclicDegreeSevenIndexApply
import PolynomialFormulas.LazardInvariantModularProductCoefficientCore
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic

/-! Semantic reduction of literal product rows to executable coefficients. -/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge

open scoped BigOperators
open Finset MvPolynomial
open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates
open LazardInvariantModularCyclicInvariants

set_option autoImplicit false

noncomputable section

def finsuppProductCoefficient (source : Exponent) (d : ℕ)
    (target : Exponent) : F3 :=
  ∑ a ∈ cyclicOrbitSupport source,
    ∑ t ∈ powersetCard d (univ : Finset (Fin 6)),
      if (∑ i ∈ t, Finsupp.single i 1) +
          Finsupp.equivFunOnFinite.symm a =
          Finsupp.equivFunOnFinite.symm target
      then 1 else 0

theorem finsuppProductCoefficient_eq_semanticProductCoefficient
    (source : Exponent) (d : ℕ) (target : Exponent) :
    finsuppProductCoefficient source d target =
      semanticProductCoefficient source d target := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro t ht
  have heq :
      (∑ i ∈ t, Finsupp.single i 1) +
          Finsupp.equivFunOnFinite.symm a =
          Finsupp.equivFunOnFinite.symm target ↔
        addExponent (subsetExponent t) a = target := by
    constructor
    · intro h
      funext i
      have hi := congrArg (fun m : Fin 6 →₀ ℕ => m i) h
      simpa [subsetExponent, addExponent, Finsupp.single_apply] using hi
    · intro h
      apply Finsupp.ext
      intro i
      have hi := congrFun h i
      simpa [subsetExponent, addExponent, Finsupp.single_apply] using hi
  rw [if_congr heq rfl rfl]

/-- The explicit coefficient formula is the actual coefficient of the
elementary-symmetric product with a cyclic orbit sum. -/
theorem coeff_esymm_mul_cyclicOrbitPolynomial
    (source : Exponent) (d : ℕ) (target : Exponent) :
    (MvPolynomial.esymm (Fin 6) F3 d *
        cyclicOrbitPolynomial source).coeff
          (Finsupp.equivFunOnFinite.symm target) =
      semanticProductCoefficient source d target := by
  rw [MvPolynomial.esymm_eq_sum_monomial]
  rw [← finsuppProductCoefficient_eq_semanticProductCoefficient]
  simp [cyclicOrbitPolynomial, finsuppProductCoefficient,
    Finset.sum_mul, Finset.mul_sum, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]

theorem esymm_isHomogeneous (d : ℕ) :
    (MvPolynomial.esymm (Fin 6) F3 d).IsHomogeneous d := by
  rw [MvPolynomial.esymm]
  apply IsHomogeneous.sum
  intro t ht
  have hcard : t.card = d := (Finset.mem_powersetCard.mp ht).2
  have hproduct := IsHomogeneous.prod t
    (fun i : Fin 6 => MvPolynomial.X i)
    (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X F3 i)
  simpa [hcard] using hproduct

theorem cyclicOrbitPolynomial_isHomogeneous_of_sum
    (source : Exponent) (n : ℕ)
    (hsource : ∑ i : Fin 6, source i = n) :
    (cyclicOrbitPolynomial source).IsHomogeneous n := by
  apply IsHomogeneous.sum
  intro a ha
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum]
  simp only [cyclicOrbitSupport, List.mem_toFinset, cyclicOrbit,
    List.mem_eraseDups, List.mem_map] at ha
  rcases ha with ⟨k, hk, rfl⟩
  change (∑ i : Fin 6, rotateExponent source k i) = n
  rw [sum_rotateExponent_of_lt_six source k (List.mem_range.mp hk), hsource]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem degreeSevenProductSource_totalDegree :
    ∀ i : Fin 159,
      (degreeSevenProductSource i).1 +
        (∑ x : Fin 6, (degreeSevenProductSource i).2 x) = 7 := by
  decide

theorem degreeSevenLiteralProduct_isHomogeneous (i : Fin 159) :
    (degreeSevenLiteralProduct i).IsHomogeneous 7 := by
  have hsource := degreeSevenProductSource_totalDegree i
  have horbit := cyclicOrbitPolynomial_isHomogeneous_of_sum
    (degreeSevenProductSource i).2
    (∑ x : Fin 6, (degreeSevenProductSource i).2 x) rfl
  have hproduct := (esymm_isHomogeneous (degreeSevenProductSource i).1).mul horbit
  simpa [degreeSevenLiteralProduct, hsource] using hproduct

theorem degreeSevenLiteralProduct_fixed (i : Fin 159) :
    cycleSixRenameLinear (degreeSevenLiteralProduct i) =
      degreeSevenLiteralProduct i := by
  have horbit :
      MvPolynomial.rename cycleSixGeneratorPermutation
          (cyclicOrbitPolynomial (degreeSevenProductSource i).2) =
        cyclicOrbitPolynomial (degreeSevenProductSource i).2 := by
    simpa using cyclicOrbitPolynomial_fixed_general
      (degreeSevenProductSource i).2
  change MvPolynomial.rename cycleSixGeneratorPermutation
      (MvPolynomial.esymm (Fin 6) F3 (degreeSevenProductSource i).1 *
        cyclicOrbitPolynomial (degreeSevenProductSource i).2) =
      MvPolynomial.esymm (Fin 6) F3 (degreeSevenProductSource i).1 *
        cyclicOrbitPolynomial (degreeSevenProductSource i).2
  rw [map_mul, MvPolynomial.rename_esymm, horbit]

theorem degreeSevenOrbitCoordinateMap_coefficients_eq_reconstruction
    (p : MvPolynomial (Fin 6) F3) :
    degreeSevenOrbitCoordinateMap (fun j =>
        p.coeff (Finsupp.equivFunOnFinite.symm
          (degreeSevenRepresentative j))) =
      degreeSevenOrbitReconstruction p := by
  rw [degreeSevenOrbitCoordinateMap, Fintype.linearCombination_apply,
    degreeSevenOrbitReconstruction]
  apply Fintype.sum_equiv degreeSevenIndexEquivOrbitRepresentative
  intro j
  simp [degreeSevenOrbitPolynomial]

/-- Once all 132 representative coefficients of a row agree with the
semantic coefficient formula, cyclic fixedness and degree-seven
reconstruction prove equality of the actual polynomials. -/
theorem degreeSevenLiteralProduct_eq_encoded_of_coefficients
    (i : Fin 159)
    (hrow : ∀ j : Fin 132,
      degreeSevenProductRow i j =
        semanticProductCoefficient (degreeSevenProductSource i).2
          (degreeSevenProductSource i).1 (degreeSevenRepresentative j)) :
    degreeSevenLiteralProduct i = degreeSevenEncodedProduct i := by
  let p := degreeSevenLiteralProduct i
  have hcoordinates :
      (fun j : Fin 132 => p.coeff
        (Finsupp.equivFunOnFinite.symm (degreeSevenRepresentative j))) =
        degreeSevenProductRow i := by
    funext j
    change (degreeSevenLiteralProduct i).coeff
      (Finsupp.equivFunOnFinite.symm (degreeSevenRepresentative j)) = _
    rw [degreeSevenLiteralProduct,
      coeff_esymm_mul_cyclicOrbitPolynomial]
    exact (hrow j).symm
  calc
    degreeSevenLiteralProduct i = degreeSevenOrbitReconstruction p :=
      (degreeSevenOrbitReconstruction_eq p
        (degreeSevenLiteralProduct_isHomogeneous i)
        (degreeSevenLiteralProduct_fixed i)).symm
    _ = degreeSevenOrbitCoordinateMap (fun j =>
        p.coeff (Finsupp.equivFunOnFinite.symm
          (degreeSevenRepresentative j))) :=
      (degreeSevenOrbitCoordinateMap_coefficients_eq_reconstruction p).symm
    _ = degreeSevenOrbitCoordinateMap (degreeSevenProductRow i) := by
      rw [hcoordinates]
    _ = degreeSevenEncodedProduct i :=
      (degreeSevenEncodedProduct_eq_coordinateMap i).symm

end


end LeanProofs.PolynomialFormulas.LazardInvariantModularProductBridge
