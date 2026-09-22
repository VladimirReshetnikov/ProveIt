import Surreal.Foundations.SmallNormalFormRealClosed

/-!
# Real closedness of the actual sign field

The ordered field normal-form equivalence transfers the unconditionally
proved odd-degree root theorem to actual sign-sequence surreals. Together
with the existing genetic construction of nonnegative square roots this
establishes real closedness of the actual field, rather than a reduction
which assumes closedness of its polynomial residue field.
-/

universe u

namespace Surreal.Foundations.SignSequence

open Polynomial

noncomputable section

/-- Every odd-degree polynomial over the actual sign field has an actual root. -/
theorem exists_isRoot_of_odd_natDegree (P : Polynomial SignSequence.{u})
    (hodd : Odd P.natDegree) : ∃ x : SignSequence.{u}, P.IsRoot x := by
  let f := SmallNormalForm.cutEvaluationRingEquiv.symm.toRingHom
  have hd : (P.map f).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective SmallNormalForm.cutEvaluationRingEquiv.symm.injective P
  obtain ⟨x, hx⟩ := SmallNormalForm.exists_isRoot_of_odd_natDegree (P.map f)
    (by simpa only [hd] using hodd)
  refine ⟨SmallNormalForm.cutEvaluation x, ?_⟩
  refine Polynomial.IsRoot.of_map (f := f) ?_ f.injective
  change (P.map f).IsRoot (SmallNormalForm.normalForm (SmallNormalForm.cutEvaluation x))
  rw [SmallNormalForm.normalForm_cutEvaluation]
  exact hx

/-- Actual surreal arithmetic is real closed, with both root properties proved. -/
instance signSequenceIsRealClosed : IsRealClosed SignSequence.{u} :=
  IsRealClosed.of_linearOrderedField
    (fun {x} hx => ⟨sqrt x, by simpa only [pow_two] using (sqrt_sq hx).symm⟩)
    (fun hodd => exists_isRoot_of_odd_natDegree _ hodd)

end

end Surreal.Foundations.SignSequence
