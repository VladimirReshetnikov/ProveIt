import PolynomialFormulas.Fin5TransitiveClassification
import PolynomialFormulas.QuinticScalarResolventCriterion

/-!
# The Section 5 subgroup classification and the quintic resolvent criterion

This file packages the two group-theoretic ingredients used together in
Section 5 of Lazard's paper.

* Every transitive subgroup of `S₅` is conjugate to exactly one of `C₅`,
  `D₅`, `F₂₀`, `A₅`, and `S₅`.
* Such a subgroup is solvable exactly when it is contained in a conjugate of
  `F₂₀`.
* For an irreducible rational quintic, the scalar Frobenius--Dummit resolvent
  has a rational root exactly when its root-permutation group satisfies that
  conjugate-`F₂₀` condition.

The conjugate in the last two statements is essential: an arbitrary ordering
of the roots need not put the permutation image inside the displayed standard
copy of `F₂₀`.
-/

open scoped Polynomial

namespace LeanProofs.PolynomialFormulas.LazardSection5ClassificationResolventBridge

namespace Classification
export LeanProofs.PolynomialFormulas.Fin5TransitiveClassification
  (S5 standardF20 TransitiveClass IsConjugateTo classSubgroup
    transitive_classification proper_transitive_classification)
end Classification

namespace TransitiveCriterion
export LeanProofs.PolynomialFormulas.Fin5TransitiveC5
  (solvable_iff_le_conjugate_standardF20)
end TransitiveCriterion

namespace Galois
export LeanProofs.PolynomialFormulas.QuinticScalarGaloisBridge
  (rootPermutationGroup rootTuple rootPermutationGroup_isPretransitive
    gal_isSolvable_iff_le_conjugate_standardF20)
end Galois

namespace ScalarCriterion
export LeanProofs.PolynomialFormulas.QuinticScalarResolventCriterion
  (scalarResolvent_has_rational_root_iff_gal_isSolvable)
end ScalarCriterion

namespace FDR
export LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent
  (scalarResolvent)
end FDR

open Equiv

abbrev S5 := Classification.S5
abbrev standardF20 : Subgroup S5 := Classification.standardF20

/-- The complete five-class classification and the solvability criterion,
stated together for an arbitrary transitive subgroup of `S₅`.  Lazard's
four-class list is obtained from the first conjunct only after adding
properness, via `Classification.proper_transitive_classification`. -/
theorem transitive_classification_and_solvability_criterion
    (H : Subgroup S5) [MulAction.IsPretransitive H (Fin 5)] :
    (∃! c : Classification.TransitiveClass,
        Classification.IsConjugateTo H (Classification.classSubgroup c)) ∧
      (IsSolvable H ↔
        ∃ g : S5,
          H ≤ standardF20.map (MulAut.conj g).toMonoidHom) := by
  exact ⟨Classification.transitive_classification H,
    TransitiveCriterion.solvable_iff_le_conjugate_standardF20 H⟩

/-- For an irreducible rational quintic, the complete classification of its
transitive root-permutation image and the scalar-resolvent test are compatible
in one theorem.  The second conjunct is the precise corrected Section 5
criterion: a rational resolvent root detects containment in *some conjugate*
of `F₂₀`, not necessarily in the displayed standard subgroup. -/
theorem irreducibleQuintic_classification_and_resolvent_criterion
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    (∃! c : Classification.TransitiveClass,
        Classification.IsConjugateTo
          (Galois.rootPermutationGroup p hp hdeg)
          (Classification.classSubgroup c)) ∧
      ((∃ q : ℚ,
          (FDR.scalarResolvent (Galois.rootTuple p hp hdeg)).IsRoot
            (algebraMap ℚ p.SplittingField q)) ↔
        ∃ g : S5,
          Galois.rootPermutationGroup p hp hdeg ≤
            standardF20.map (MulAut.conj g).toMonoidHom) := by
  letI : MulAction.IsPretransitive
      (Galois.rootPermutationGroup p hp hdeg) (Fin 5) :=
    Galois.rootPermutationGroup_isPretransitive p hp hdeg
  constructor
  · exact Classification.transitive_classification
      (Galois.rootPermutationGroup p hp hdeg)
  · exact
      (ScalarCriterion.scalarResolvent_has_rational_root_iff_gal_isSolvable
        p hp hdeg).trans
        (Galois.gal_isSolvable_iff_le_conjugate_standardF20 p hp hdeg)

end LeanProofs.PolynomialFormulas.LazardSection5ClassificationResolventBridge
