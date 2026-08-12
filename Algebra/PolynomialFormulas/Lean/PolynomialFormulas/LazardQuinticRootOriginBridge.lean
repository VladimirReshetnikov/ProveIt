import PolynomialFormulas.LazardQuinticDeterminantBridge
import PolynomialFormulas.LazardQuinticInvariantDescent
import PolynomialFormulas.LazardQuinticInvariantSystemMap
import PolynomialFormulas.LazardQuinticRootOrdering

/-!
# Rational Lazard invariants from an ordered root tuple

For an irreducible depressed rational quintic, a rational root of Lazard's
sextic selects an ordering of the five splitting-field roots whose first
metacyclic invariant is rational.  The root identities give all five
invariant equations, the discriminant certificate makes the Figure-3 system
nonsingular, and Galois descent then shows that the complete invariant tuple
comes from `ℚ`.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open ComputableDummitCoefficients
open QuinticScalarGaloisBridge

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

/-- For the actual canonical root tuple, irreducibility alone supplies the
Figure-3 determinant needed to make the remaining four invariants unique once
`i₄` is fixed.  No determinant or relation certificate for the root-defined
tuple is accepted from the caller. -/
theorem rootTuple_invariants_unique_from_i4
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (j : Invariants c.polynomial.SplittingField)
    (hj : InvariantRelations
      (c.map (algebraMap ℚ c.polynomial.SplittingField)) j)
    (hi4 :
      (rootInvariants
        (rootTuple c.polynomial hp c.polynomial_natDegree)).i4 = j.i4) :
    rootInvariants (rootTuple c.polynomial hp c.polynomial_natDegree) = j := by
  let φ := algebraMap ℚ c.polynomial.SplittingField
  let x := rootTuple c.polynomial hp c.polynomial_natDegree
  have helementary :
      elementaryTuple x = depressedElementary (c.map φ) := by
    exact elementaryTuple_rootTuple_eq_depressedElementary c hp
  have hsum : elementaryTuple x 0 = 0 := by
    rw [helementary]
    simp [depressedElementary]
  have hc : depressedOfRoots x = c.map φ :=
    depressedOfRoots_eq_of_elementaryTuple_eq (c.map φ) x helementary
  have hrelations : InvariantRelations (c.map φ) (rootInvariants x) := by
    rw [← hc]
    exact rootInvariantRelations x hsum
  have hdet : (invariantSystemMatrix (c.map φ)).det ≠ 0 :=
    invariantSystemMatrix_det_ne_zero_map c φ
      (invariantSystemMatrix_det_ne_zero c hp)
  exact hrelations.eq_of_i4_eq_of_det_ne_zero hj hi4 hdet

/-- Fully root-origin Figure-3 uniqueness for two of the six canonical
representative orderings.  Both relation packages and determinant
nonvanishing are derived internally; the caller supplies only equality of
the two selected `i₄` values. -/
theorem representativeRootTuple_invariants_eq_of_i4_eq
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (i k : Fin 6)
    (hi4 :
      (rootInvariants (fun j ↦
        rootTuple c.polynomial hp c.polynomial_natDegree
          (FrobeniusDummitResolvent.representative i j))).i4 =
      (rootInvariants (fun j ↦
        rootTuple c.polynomial hp c.polynomial_natDegree
          (FrobeniusDummitResolvent.representative k j))).i4) :
    rootInvariants (fun j ↦
      rootTuple c.polynomial hp c.polynomial_natDegree
        (FrobeniusDummitResolvent.representative i j)) =
    rootInvariants (fun j ↦
      rootTuple c.polynomial hp c.polynomial_natDegree
        (FrobeniusDummitResolvent.representative k j)) := by
  let φ := algebraMap ℚ c.polynomial.SplittingField
  let baseRoots := rootTuple c.polynomial hp c.polynomial_natDegree
  let xi : Fin 5 → c.polynomial.SplittingField := fun j ↦
    baseRoots (FrobeniusDummitResolvent.representative i j)
  let xk : Fin 5 → c.polynomial.SplittingField := fun j ↦
    baseRoots (FrobeniusDummitResolvent.representative k j)
  have hbase : elementaryTuple baseRoots =
      depressedElementary (c.map φ) :=
    elementaryTuple_rootTuple_eq_depressedElementary c hp
  have hei : elementaryTuple xi = depressedElementary (c.map φ) := by
    rw [show elementaryTuple xi = elementaryTuple baseRoots by
      exact elementaryTuple_representative baseRoots i]
    exact hbase
  have hek : elementaryTuple xk = depressedElementary (c.map φ) := by
    rw [show elementaryTuple xk = elementaryTuple baseRoots by
      exact elementaryTuple_representative baseRoots k]
    exact hbase
  have hci : depressedOfRoots xi = c.map φ :=
    depressedOfRoots_eq_of_elementaryTuple_eq (c.map φ) xi hei
  have hck : depressedOfRoots xk = c.map φ :=
    depressedOfRoots_eq_of_elementaryTuple_eq (c.map φ) xk hek
  have hsumi : elementaryTuple xi 0 = 0 := by
    rw [hei]
    simp [depressedElementary]
  have hsumk : elementaryTuple xk 0 = 0 := by
    rw [hek]
    simp [depressedElementary]
  have hri : InvariantRelations (c.map φ) (rootInvariants xi) := by
    rw [← hci]
    exact rootInvariantRelations xi hsumi
  have hrk : InvariantRelations (c.map φ) (rootInvariants xk) := by
    rw [← hck]
    exact rootInvariantRelations xk hsumk
  have hdet : (invariantSystemMatrix (c.map φ)).det ≠ 0 :=
    invariantSystemMatrix_det_ne_zero_map c φ
      (invariantSystemMatrix_det_ne_zero c hp)
  exact hri.eq_of_i4_eq_of_det_ne_zero hrk hi4 hdet

/-- End-to-end root-origin construction of Lazard's rational invariant
certificate.  No rationality of `i₅,…,i₈` is assumed: it follows from the
root identities and uniqueness of the nonsingular Figure-3 system. -/
theorem exists_rootOrdering_and_rational_invariants
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (hq : ∃ q : ℚ, (resolventPolynomial c).IsRoot q) :
    ∃ (x : Fin 5 → c.polynomial.SplittingField) (j : Invariants ℚ),
      Function.Injective x ∧
      elementaryTuple x = depressedElementary
        (c.map (algebraMap ℚ c.polynomial.SplittingField)) ∧
      InvariantRelations c j ∧
      j.map (algebraMap ℚ c.polynomial.SplittingField) = rootInvariants x ∧
      ∀ omega : FifthRootOfUnity c.polynomial.SplittingField,
        rootEpsilon omega x ≠ 0 := by
  obtain ⟨x, hx, helementary, q, hi4, hepsilon⟩ :=
    exists_rootOrdering_with_rational_i4_and_rootEpsilon_ne_zero c hp hq
  let φ := algebraMap ℚ c.polynomial.SplittingField
  have hsum : elementaryTuple x 0 = 0 := by
    rw [helementary]
    simp [depressedElementary]
  have hc : depressedOfRoots x = c.map φ :=
    depressedOfRoots_eq_of_elementaryTuple_eq (c.map φ) x helementary
  have hrelations : InvariantRelations (c.map φ) (rootInvariants x) := by
    rw [← hc]
    exact rootInvariantRelations x hsum
  have hdet : (invariantSystemMatrix (c.map φ)).det ≠ 0 :=
    invariantSystemMatrix_det_ne_zero_map c φ
      (invariantSystemMatrix_det_ne_zero c hp)
  obtain ⟨j, hj, hjmap⟩ :=
    exists_rational_invariants_of_i4_rational c hp (rootInvariants x)
      hrelations hdet ⟨q, hi4⟩
  exact ⟨x, j, hx, helementary, hj, hjmap, hepsilon⟩

end

end LeanProofs.PolynomialFormulas.LazardQuintic
