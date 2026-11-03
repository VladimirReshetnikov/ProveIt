import DirectBFSRowTransfer
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSEdgeForward
open DirectBFSConjugacyBase DirectBFSConjugacyLift DirectBFSRowTransfer

theorem original_is_renamed_direct (i : Fin 943) :
    rename (Compact943Data.row i)=DirectBFSSymbolicKernel.row (rowForward i) := by
  have h := row_match_fin i
  rw [original_row,direct_row] at h
  exact h

theorem horizontal (a b : Fin 943)
    (h : (Compact943Data.row a).2.2.1=(Compact943Data.row b).1) :
    (DirectBFSSymbolicKernel.row (rowForward a)).2.2.1=(DirectBFSSymbolicKernel.row (rowForward b)).1 := by
  have ha := congrArg (fun t => t.2.2.1) (original_is_renamed_direct a)
  have hb := congrArg (fun t => t.1) (original_is_renamed_direct b)
  have he := congrArg (fun x => DirectBFSConjugacyBase.horizontal.getD x 0) h
  exact ha.symm.trans (he.trans hb)

theorem vertical (a b : Fin 943)
    (h : (Compact943Data.row a).2.2.2=(Compact943Data.row b).2.1) :
    (DirectBFSSymbolicKernel.row (rowForward a)).2.2.2=(DirectBFSSymbolicKernel.row (rowForward b)).2.1 := by
  have ha := congrArg (fun t => t.2.2.2) (original_is_renamed_direct a)
  have hb := congrArg (fun t => t.2.1) (original_is_renamed_direct b)
  have he := congrArg (fun x => DirectBFSConjugacyBase.vertical.getD x 0) h
  exact ha.symm.trans (he.trans hb)
#print axioms DirectBFSEdgeForward.original_is_renamed_direct
#print axioms DirectBFSEdgeForward.horizontal
#print axioms DirectBFSEdgeForward.vertical
end DirectBFSEdgeForward
