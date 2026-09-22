import Surreal.Algebra.RealPolynomialFactors
import Surreal.Algebra.PolynomialDepression
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Real closedness of the ordinary real coefficient field

The pinned Mathlib supplies the real-closed-field interface but no instance
for the ordinary reals. Its square-root theorem and polynomial consequences
of the intermediate value theorem provide the two required properties.
This instantiates the coefficient hypothesis of the real Hahn construction.
-/

namespace Surreal.FinitePolynomial

open Polynomial

/-- The monic real odd-root theorem extends to every odd-degree polynomial. -/
theorem real_odd_exists_root {P : ℝ[X]} (hodd : Odd P.natDegree) :
    ∃ a : ℝ, P.IsRoot a := by
  have hP : P ≠ 0 := by
    intro h
    simp only [h, natDegree_zero, Nat.not_odd_zero] at hodd
  obtain ⟨a, ha⟩ := real_monic_odd_exists_root (monic_monicNormalize hP)
    (by simpa only [natDegree_monicNormalize hP] using hodd)
  exact ⟨a, (isRoot_monicNormalize_iff hP a).mp ha⟩

/-- The ordinary real field is real closed, using its actual square roots and
the intermediate value theorem rather than an assumed closedness instance. -/
instance realIsRealClosed : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField
    (fun {x} hx => ⟨Real.sqrt x, by simpa only [pow_two] using (Real.sq_sqrt hx).symm⟩)
    (fun hodd => real_odd_exists_root hodd)

end Surreal.FinitePolynomial
