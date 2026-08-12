import PolynomialFormulas.LazardQuinticGeneralEndToEnd
import PolynomialFormulas.LazardQuinticGeneralSolvabilityTransport

/-!
# Solvability transport for a general rational quintic

`LazardQuinticGeneralSolvabilityTransport` independently transports complete
radical solvability through depression and supplies the rational resolvent
root.  This file composes that shared result with the standard printed
`E ≠ 0` end-to-end formula path.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open Polynomial IntermediateField

set_option autoImplicit false

noncomputable section

/-- Original-polynomial solvability to explicit Lazard output, with one
radical field containing all five pairwise-distinct displayed values, their
exact multiplicity-sensitive factorization, and root-set soundness and
exhaustiveness. -/
theorem
    exists_radicalFormula_completeRootVector_of_completelySolvableByRadicals
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial)
    (hsolvable : CompletelySolvableByRadicals c.polynomial) :
    ∃ (roots : Fin 5 → ℂ) (L : IntermediateField ℚ ℂ),
      LazardOptimality.IsRadicalExtension ℚ ℂ
        (⊥ : IntermediateField ℚ ℂ) L ∧
      (∀ k, roots k ∈ L) ∧
      Function.Injective roots ∧
      ((c.map (algebraMap ℚ ℂ)).polynomial =
        Polynomial.C (algebraMap ℚ ℂ c.a) *
          ∏ k : Fin 5, (Polynomial.X - Polynomial.C (roots k))) ∧
      (∀ z : ℂ,
        (c.map (algebraMap ℚ ℂ)).eval z = 0 ↔
          ∃ k : Fin 5, z = roots k) := by
  apply exists_radicalFormula_completeRootVector c ha hp
  exact exists_depressed_resolvent_root_of_completelySolvableByRadicals
    c ha hp hsolvable

end

end LeanProofs.PolynomialFormulas.LazardQuintic
