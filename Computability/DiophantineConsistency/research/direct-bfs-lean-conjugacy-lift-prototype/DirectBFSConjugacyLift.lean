import DirectBFSCoverageAggregate
import DirectBFSConjugacyShape

/-! Pointwise reading of the complete checked finite conjugacy certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSConjugacyLift
open DirectBFSConjugacyBase DirectBFSConjugacyChunk DirectBFSCoverageAggregate

private theorem mem_range0 {i n : Nat} (h : i<n) : i ∈ List.range' 0 n := by
  apply List.mem_range'.2
  exact ⟨i,h,by simp⟩

theorem row_match {i : Nat} (hi : i<943) :
    rename (original.getD i (0,0,0,0))=direct.getD (rowMap.getD i 0) (0,0,0,0) := by
  have h := rows_all
  unfold checkRows at h
  exact of_decide_eq_true ((List.all_eq_true.mp h) i (mem_range0 hi))

theorem row_inverse {i : Nat} (hi : i<943) : rowMap.getD (rowInverse.getD i 0) 0=i := by
  have h := inverse_all
  unfold checkRowInverse at h
  exact of_decide_eq_true ((List.all_eq_true.mp h) i (mem_range0 hi))

theorem row_bounds {i : Nat} (hi : i<943) : rowMap.getD i 0<943 ∧ rowInverse.getD i 0<943 := by
  exact of_decide_eq_true ((List.all_eq_true.mp inversebounds_all) i (mem_range0 hi))

theorem horizontal_inverse {i : Nat} (hi : i<250) :
    horizontal.getD (horizontalInverse.getD i 0) 0=i := by
  have h := horizontal_all
  unfold checkHorizontal at h
  exact of_decide_eq_true ((List.all_eq_true.mp h) i (mem_range0 hi))

theorem horizontal_bounds {i : Nat} (hi : i<250) :
    horizontal.getD i 0<250 ∧ horizontalInverse.getD i 0<250 := by
  exact of_decide_eq_true ((List.all_eq_true.mp horizontalbounds_all) i (mem_range0 hi))

theorem vertical_inverse {i : Nat} (hi : i<439) : vertical.getD (verticalInverse.getD i 0) 0=i := by
  have h := vertical_all
  unfold checkVertical at h
  exact of_decide_eq_true ((List.all_eq_true.mp h) i (mem_range0 hi))

theorem vertical_bounds {i : Nat} (hi : i<439) : vertical.getD i 0<439 ∧ verticalInverse.getD i 0<439 := by
  exact of_decide_eq_true ((List.all_eq_true.mp verticalbounds_all) i (mem_range0 hi))


noncomputable def rowForward (i : Fin 943) : Fin 943 := ⟨rowMap.getD i.val 0,(row_bounds i.isLt).1⟩
noncomputable def rowBackward (i : Fin 943) : Fin 943 := ⟨rowInverse.getD i.val 0,(row_bounds i.isLt).2⟩
noncomputable def horizontalForward (i : Fin 250) : Fin 250 := ⟨horizontal.getD i.val 0,(horizontal_bounds i.isLt).1⟩
noncomputable def horizontalBackward (i : Fin 250) : Fin 250 := ⟨horizontalInverse.getD i.val 0,(horizontal_bounds i.isLt).2⟩
noncomputable def verticalForward (i : Fin 439) : Fin 439 := ⟨vertical.getD i.val 0,(vertical_bounds i.isLt).1⟩
noncomputable def verticalBackward (i : Fin 439) : Fin 439 := ⟨verticalInverse.getD i.val 0,(vertical_bounds i.isLt).2⟩

theorem row_bijective : Function.Bijective rowForward := by
  have hs : Function.Surjective rowForward := fun i => ⟨rowBackward i,Fin.ext (row_inverse i.isLt)⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs,hs⟩

theorem horizontal_bijective : Function.Bijective horizontalForward := by
  have hs : Function.Surjective horizontalForward := fun i => ⟨horizontalBackward i,Fin.ext (horizontal_inverse i.isLt)⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs,hs⟩

theorem vertical_bijective : Function.Bijective verticalForward := by
  have hs : Function.Surjective verticalForward := fun i => ⟨verticalBackward i,Fin.ext (vertical_inverse i.isLt)⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs,hs⟩

theorem row_match_fin (i : Fin 943) :
    rename (original.getD i.val (0,0,0,0))=direct.getD (rowForward i).val (0,0,0,0) :=
  row_match i.isLt

#print axioms DirectBFSConjugacyLift.row_bijective
#print axioms DirectBFSConjugacyLift.horizontal_bijective
#print axioms DirectBFSConjugacyLift.vertical_bijective
#print axioms DirectBFSConjugacyLift.row_match_fin

#print axioms DirectBFSConjugacyLift.row_match
#print axioms DirectBFSConjugacyLift.row_inverse
#print axioms DirectBFSConjugacyLift.row_bounds
#print axioms DirectBFSConjugacyLift.horizontal_inverse
#print axioms DirectBFSConjugacyLift.horizontal_bounds
#print axioms DirectBFSConjugacyLift.vertical_inverse
#print axioms DirectBFSConjugacyLift.vertical_bounds
end DirectBFSConjugacyLift
