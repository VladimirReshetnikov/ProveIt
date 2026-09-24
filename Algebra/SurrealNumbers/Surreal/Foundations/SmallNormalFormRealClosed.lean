import Surreal.Foundations.SmallNormalFormWorkspace
import Surreal.Foundations.SmallNormalFormFieldEquiv
import Surreal.Foundations.SignSequenceRoots

/-!
# Real closedness of the small formal normal-form field

Every polynomial's coefficients lie in one small divisible real Hahn
workspace. The injective workspace embedding preserves its degree, and the
proved Hahn odd-root theorem supplies a root of every odd-degree polynomial.
Nonnegative squares come from the independently constructed actual sign
roots through the ordered field equivalence. Neither field's real closedness
is assumed in these constructions.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open Polynomial SignSequence

noncomputable section

/-- Odd-degree polynomial roots are obtained in a common coefficient workspace. -/
theorem exists_isRoot_of_odd_natDegree (P : Polynomial SmallNormalForm.{u})
    (hodd : Odd P.natDegree) : ∃ x : SmallNormalForm.{u}, P.IsRoot x := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_hahn_preimage P
  let f := familyWorkspaceEmbedding P.coeff
  have hd : Q.natDegree = P.natDegree := by
    have h := natDegree_map_eq_of_injective (familyWorkspaceEmbedding_injective P.coeff) Q
    rw [hQ] at h
    exact h.symm
  obtain ⟨x, hx⟩ := Surreal.HahnSeries.exists_isRoot_of_odd_natDegree Q
    (by simpa only [hd] using hodd)
  refine ⟨f x, ?_⟩
  simpa only [hQ] using (hx.map (f := familyWorkspaceEmbedding P.coeff))

/-- The already constructed sign-field square roots transport to the formal field. -/
theorem isSquare_of_nonneg {x : SmallNormalForm.{u}} (hx : 0 ≤ x) : IsSquare x := by
  have he : 0 ≤ cutEvaluation x := by
    simpa only [cutEvaluation_zero] using (cutEvaluation_le_iff 0 x).mpr hx
  obtain ⟨y, _, hy⟩ := SignSequence.exists_nonneg_sq (cutEvaluation x) he
  refine ⟨normalForm y, ?_⟩
  apply cutEvaluation_injective
  simpa only [cutEvaluation_mul, cutEvaluation_normalForm, pow_two] using hy.symm

/-- The full small-support formal Hahn field is real closed. -/
instance smallNormalFormIsRealClosed : IsRealClosed SmallNormalForm.{u} :=
  IsRealClosed.of_linearOrderedField isSquare_of_nonneg
    (fun hodd => exists_isRoot_of_odd_natDegree _ hodd)

end

end Surreal.Foundations.SmallNormalForm
